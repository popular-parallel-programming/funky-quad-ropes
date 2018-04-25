module Shim =
  struct
    let (>>) f g =
      fun x -> f (g x)

    let ($) f x = f x

    let uncurry f =
      fun (x, y) -> f x y
  end


module Array2D =
  struct
    type 'a array2d = 'a array array

    open Shim

    let init rows cols f : _ array2d =
      Array.init rows $ fun i -> Array.init cols (f i)

    let get (xss : _ array2d) i j =
      Array.get (Array.get xss i) j

    let map f xss : _ array2d =
      Array.map (fun xs -> Array.map f xs) xss

    let mapi f xss : _ array2d =
      Array.mapi (fun i xs -> Array.mapi (fun j x -> f i j x) xs) xss

    let zipWith f (xss0 : _ array2d) (xss1 : _ array2d) : _ array2d =
      mapi (fun i j x -> f x (get xss1 i j)) xss0

    let rows (xss : _ array2d) =
      Array.length xss

    let cols (xss : _ array2d) = (* Assume all columns are of equal length. *)
      Array.length $ Array.get xss 0

    let slice (xss : _ array2d) r0 r1 c0 c1 =
      init r1 c1 $ fun r c -> get xss (r0 + r) (c0 + c)

    let mapi_reduce f g e (xss : _ array2d) =
      let rec loop r c acc =
        if c = cols xss then loop (r + 1) 0 acc else (* Next row. *)
        if r = rows xss then acc else                (* Done. *)
        loop r (c + 1) (g acc (f r c (get xss r c))) (* Next column. *)
      in loop 0 0 e

    let map_reduce f = mapi_reduce (fun _ _ x -> f x)
    let reduce = map_reduce (fun x -> x)
  end


module QuadRope =
  struct

    open Shim

    type _ quad_rope =
      | Funk : (int -> int -> 'a -> 'b) * 'a quad_rope * 'b quad_rope lazy_t -> 'b quad_rope
      | Leaf : 'a Array2D.array2d -> 'a quad_rope
      | HCat : 'a quad_rope * 'a quad_rope -> 'a quad_rope
      | VCat : 'a quad_rope * 'a quad_rope -> 'a quad_rope
      | Sparse : int * int * 'a -> 'a quad_rope


    let rec rows : 'a . 'a quad_rope -> int = function
      | Funk (_, q, _) -> rows q
      | Leaf xss -> Array2D.rows xss
      | HCat (q1, q2) -> rows q1 (* rows q1 = rows q2 *)
      | VCat (q1, q2) -> rows q1 + rows q2
      | Sparse (r, _, _) -> r


    let rec cols : 'a . 'a quad_rope -> int = function
      | Funk (_, q, _) -> cols q
      | Leaf xss -> Array2D.cols xss
      | HCat (q1, q2) -> cols q1 + cols q2
      | VCat (q1, q2) -> cols q1 (* cols q1 = cols q2 *)
      | Sparse (_, c, _) -> c


    let hcat q1 q2 = if rows q1 = rows q2 then HCat (q1, q2) else failwith "Not same number of rows"
    let vcat q1 q2 = if cols q1 = cols q2 then VCat (q1, q2) else failwith "Not same number of columns"


    let init rows cols f =
      let max_size = 4 in
      let rec init row_off col_off rows cols =
        if rows < max_size && cols < max_size then
          Leaf (Array2D.init rows cols (fun r c -> f (r + row_off) (c + col_off)))
        else if rows < cols then
          let c2 = cols / 2 in
          hcat (init row_off col_off rows c2) (init row_off (col_off + c2) rows (cols - c2))
        else
          let r2 = rows / 2 in
          vcat (init row_off col_off r2 cols) (init (row_off + r2) col_off (rows - r2) cols)
      in init 0 0 rows cols


    let mapi f =
      let rec mapi_i : 'a 'b . int -> int -> (int -> int -> 'a -> 'b) -> 'a quad_rope -> 'b quad_rope =
        fun r0 c0 f -> (function
                        | Funk (g, q, thunk) ->
                           if Lazy.is_val thunk then
                             mapi_i r0 c0 f $ Lazy.force_val thunk
                           else
                             let k = fun r c x -> f r c (g r c x) in
                             mapi_i r0 c0 k q
                        | Leaf xss         -> Leaf (Array2D.mapi (fun r c x -> f (r0 + r) (c0 + c) x) xss)
                        | HCat (q1, q2)    -> HCat (mapi_i r0 c0 f q1, mapi_i r0 (c0 + cols q1) f q2)
                        | VCat (q1, q2)    -> VCat (mapi_i r0 c0 f q1, mapi_i (r0 + rows q1) c0 f q2)
                        | Sparse (r, c, x) -> init r c (fun r c -> f (r0 + r) (c0 + c) x))
      in mapi_i 0 0 f


    let rec funky_mapi : 'a 'b . (int -> int -> 'a -> 'b) -> 'a quad_rope -> 'b quad_rope =
      fun f -> (function
                | Funk (g, q, thunk) ->
                   if Lazy.is_val thunk then
                     funky_mapi f $ Lazy.force_val thunk
                   else
                     funky_mapi (fun r c x -> f r c (g r c x)) q
                | q -> Funk (f, q, lazy (mapi f q)))


    let map f = mapi (fun r c x -> f x)
    let funky_map f = funky_mapi (fun r c x -> f x)


    let replicate rows cols x = Sparse (max 0 rows, max 0 cols, x)


    let funky_init rows cols f =
      let p = replicate rows cols () in
      let g = fun r c _ -> f r c in
      funky_mapi g p


    let rec get q r c =
      match q with
      | Funk (_, _, thunk) -> get (Lazy.force_val thunk) r c
      | Leaf xss           -> Array2D.get xss r c
      | HCat (q1, q2)      -> if c < cols q1 then get q1 r c else get q2 r (c - cols q1)
      | VCat (q1, q2)      -> if r < rows q1 then get q1 r c else get q2 (r - rows q1) c
      | Sparse (_, _, x)   -> x


    let rec slice  : 'a . 'a quad_rope -> int -> int -> int -> int -> 'a quad_rope = fun q r0 r1 c0 c1 ->
      let r0, c0 = max 0 r0, max 0 c0 in
      let r1, c1 = min (rows q - r0) (max 0 r1), min (cols q - c0) (max 0 c1) in
      match q with
      | Funk (f, p, thunk) -> funky_mapi f $ slice p r0 r1 c0 c1
      | Leaf xss -> Leaf (Array2D.slice xss r0 r1 c0 c1)
      | HCat (q1, q2) ->
         let q1' = slice q1 r0 r1 c0 c1 in
         let q2' = slice q2 r0 r1 (c0 - cols q1) (c1 - cols q1') in
         hcat q1' q2'
      | VCat (q1, q2) ->
         let q1' = slice q1 r0 r1 c0 c1 in
         let q2' = slice q2 (r0 - rows q1) (r1 - rows q1') c0 c1 in
         vcat q1' q2'
      | Sparse (_, _, x) -> replicate r1 c1 x


    let mapi_reduce f g e q =
      let sparse_loop (Sparse (rows, cols, x)) r0 c0 f g e =
        let rec loop r c acc =
          if c = rows then loop (r + 1) 0 acc else       (* Next row. *)
          if r = cols then acc else                      (* Done. *)
          loop r (c + 1) (g acc (f (r + r0) (c + c0) x)) (* Next column. *)
        in loop 0 0 e
      in
      let rec mapi_reduce_i : 'a 'b . int -> int -> (int -> int -> 'a -> 'b) -> ('b -> 'b -> 'b) -> 'b -> 'a quad_rope -> 'b =
        fun r0 c0 f g e ->
        (function
         | Funk (k, q, thunk) ->
            if Lazy.is_val thunk then
              mapi_reduce_i r0 c0 f g e $ Lazy.force_val thunk
            else
              let h = fun r c x -> f r c (k r c x) in
              mapi_reduce_i r0 c0 h g e q
         | Leaf xss      -> Array2D.mapi_reduce (fun r c x -> f (r0 + r) (c0 + c) x) g e xss
         | HCat (q1, q2) -> g (mapi_reduce_i r0 c0 f g e q1) (mapi_reduce_i r0 (c0 + cols q1) f g e q2)
         | VCat (q1, q2) -> g (mapi_reduce_i r0 c0 f g e q1) (mapi_reduce_i (r0 + rows q1) c0 f g e q2)
         | Sparse (r, c, x) as q -> sparse_loop q r0 c0 f g e) (* TODO: Add recursive splitting. *)
      in mapi_reduce_i 0 0 f g e q


    let map_reduce f = mapi_reduce (fun _ _ x -> f x)
    let reduce = map_reduce (fun x -> x)
  end
