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
      Array.init rows (fun i -> Array.init cols (f i))

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
          let c2 = cols / 2 in (* TODO: This is wrong. *)
          hcat (init row_off col_off rows c2) (init row_off (col_off + c2) rows c2)
        else
          let r2 = rows / 2 in (* TODO: This is wrong. *)
          vcat (init row_off col_off r2 cols) (init (row_off + r2) col_off r2 cols)
      in init 0 0 rows cols


    let mapi f =
      let rec mapii : 'a 'b . int -> int -> (int -> int -> 'a -> 'b) -> 'a quad_rope -> 'b quad_rope =
        fun r0 c0 f -> (function
                        | Funk (g, q, thunk) ->
                           if Lazy.is_val thunk then
                             let p = Lazy.force_val thunk in
                             Funk (f, p, lazy (mapii r0 c0 f p))
                           else
                             let k = (fun r c x -> f r c (g r c x))
                             in Funk (k, q, lazy (mapii r0 c0 k q))
                        | Leaf xss         -> Leaf (Array2D.mapi (fun r c x -> f (r0 + r) (c0 + c) x) xss)
                        | HCat (q1, q2)    -> HCat (mapii r0 c0 f q1, mapii r0 (c0 + cols q1) f q2)
                        | VCat (q1, q2)    -> VCat (mapii r0 c0 f q1, mapii (r0 + rows q1) c0 f q2)
                        | Sparse (r, c, x) -> init r c (fun r c -> f (r0 + r) (c0 + c) x))
      in mapii 0 0 f


    let map f = mapi (fun r c x -> f x)
    let replicate rows cols x = Sparse (rows, cols, x)


    let lazy_init rows cols (f : int -> int -> 'a) =
      let p = replicate rows cols () in
      let g = fun r c _ -> f r c in
      Funk (g, p, lazy (mapi g p))

  end
