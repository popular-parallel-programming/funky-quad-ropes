module Shim =
  struct
    let (>>) f g =
      fun x -> f (g x)

    let ($) f x = f x

    let uncurry f =
      fun (x, y) -> f x y
  end

(* Signature for two-dimensional collections.  *)
module type Collection2D =
  sig
    type 'a t
    val init : int -> int -> (int -> int -> 'a) -> 'a t
    val get : 'a t -> int -> int -> 'a
    val rows : _ t -> int
    val cols : _ t -> int
    val hcat : 'a t -> 'a t -> 'a t
    val vcat : 'a t -> 'a t -> 'a t
    val map : ('a -> 'b) -> 'a t -> 'b t
    val zipWith : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
    val map_reduce : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'b -> 'a t -> 'b
    val reduce : ('a -> 'a -> 'a) -> 'a -> 'a t -> 'a
  end


module Array2D =
  struct
    type 'a t = 'a array array

    open Shim

    let init rows cols f : _ =
      Array.init rows $ fun i -> Array.init cols (f i)


    let get (xss : _ t) i j =
      Array.get (Array.get xss i) j

    let rows (xss : _ t) =
      Array.length xss


    let cols (xss : _ t) = (* Assume all columns are of equal length. *)
      if rows xss = 0 then 0 else Array.length $ Array.get xss 0


    let hcat xss yss =
      if rows xss = rows yss then
        init (rows xss)
             (cols xss + cols yss)
             (fun r c ->
               if c < cols xss then
                 get xss r c
               else
                 get yss r (c - cols xss))
      else
        failwith "not same number of rows"


    let vcat xss yss =
      if cols xss = cols yss then
        init (rows xss + rows yss)
             (cols xss)
             (fun r c ->
               if r < rows xss then
                 get xss r c
               else
                 get yss (r - rows xss) c)
      else
        failwith "not same number of columns"



    let map f xss : _ t =
      Array.map (fun xs -> Array.map f xs) xss


    let mapi f xss : _ t =
      Array.mapi (fun i xs -> Array.mapi (fun j x -> f i j x) xs) xss


    let zipWith f (xss0 : _ t) (xss1 : _ t) : _ t =
      mapi (fun i j x -> f x (get xss1 i j)) xss0


    let zipWithi f (xss0 : _ t) (xss1 : _ t) : _ t =
      mapi (fun i j x -> f i j x (get xss1 i j)) xss0


    let mapi_reduce (f : int -> int -> 'a -> 'b) (g : 'b -> 'b -> 'b) (e : 'b) (xss : 'a t) : 'b =
      let acc = ref e in
      for r = 0 to rows xss - 1 do
        for c = 0 to cols xss - 1 do
          acc := g !acc (f r c (get xss r c));
        done;
      done;
      !acc


    let map_reduce f =
      mapi_reduce (fun _ _ x -> f x)


    let reduce f =
      mapi_reduce (fun _ _ x -> x) f
  end


module QuadRope =
  struct

    open Shim

    type _ quad_rope =
      | Funk : (int -> int -> 'a -> 'b) * 'a quad_rope * 'b quad_rope lazy_t -> 'b quad_rope
      | Leaf : 'a Array2D.t -> 'a quad_rope
      | HCat : 'a quad_rope * 'a quad_rope -> 'a quad_rope
      | VCat : 'a quad_rope * 'a quad_rope -> 'a quad_rope
      | Sparse : int * int * 'a -> 'a quad_rope

    type 'a t = 'a quad_rope

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


    let hcat q1 q2 =
      if rows q1 = rows q2 then
        HCat (q1, q2)
      else
        failwith "not same number of rows"


    let vcat q1 q2 =
      if cols q1 = cols q2 then
        VCat (q1, q2)
      else
        failwith "not same number of columns"


    let rec get q r c =
      match q with
      | Funk (_, _, thunk) -> get (Lazy.force_val thunk) r c
      | Leaf xss           -> Array2D.get xss r c
      | HCat (q1, q2)      -> if c < cols q1 then get q1 r c else get q2 r (c - cols q1)
      | VCat (q1, q2)      -> if r < rows q1 then get q1 r c else get q2 (r - rows q1) c
      | Sparse (_, _, x)   -> x


    let init rows cols f =
      let max_size = 32 in
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


    let map f =
      mapi (fun _ _ x -> f x)


    let zipWithi f q1 q2 =
      if rows q1 <> cols q2 || cols q1 <> cols q2 then
        failwith "shape mismatch"
      else
        (* Cheap and slow; materializes Funk nodes. *)
        init (rows q1) (cols q1) (fun r c -> f r c (get q1 r c) (get q2 r c))


    let zipWith f =
      zipWithi (fun _ _ x y -> f x y)


    let replicate rows cols x =
      Sparse (max 0 rows, max 0 cols, x)

    let mapi_reduce f g e q =
      let sparse_loop rows cols x r0 c0 f g e =
        let acc = ref e in
        for r = r0 to r0 + rows - 1 do
          for c = c0 to c0 + cols - 1 do
            acc := g !acc (f r c x);
          done;
        done;
        !acc
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
         | Sparse (r, c, x) -> sparse_loop r c x r0 c0 f g e) (* TODO: Add recursive splitting. *)
      in mapi_reduce_i 0 0 f g e q


    let map_reduce f =
      mapi_reduce (fun _ _ x -> f x)


    let reduce f =
      map_reduce (fun x -> x) f
  end


module Funky =
  struct
    type 'a t = 'a QuadRope.t

    open Shim
    open QuadRope

    let rows = QuadRope.rows
    let cols = QuadRope.cols
    let get = QuadRope.get
    let hcat = QuadRope.hcat
    let vcat = QuadRope.vcat

    let rec mapi : 'a 'b . (int -> int -> 'a -> 'b) -> 'a quad_rope -> 'b quad_rope =
      fun f -> (function
                | Funk (g, q, thunk) ->
                   if Lazy.is_val thunk then
                     mapi f $ Lazy.force_val thunk
                   else
                     mapi (fun r c x -> f r c (g r c x)) q
                | q -> Funk (f, q, lazy (mapi f q)))


    let map f =
      mapi (fun r c x -> f x)


    let init rows cols f =
      let p = replicate rows cols () in
      let g = fun r c _ -> f r c in
      mapi g p


    let zipWithi f q1 q2 =
      let g =
      (match q1 with
       | Funk (f1, p1, t1) when not (Lazy.is_val t1) ->
          fun r c -> f1 r c (get p1 r c)
       | _ -> get q1)
      in
      mapi (fun r c x -> f r c (g r c) x) q2


    let zipWith f =
      zipWithi (fun _ _ x y -> f x y)


    (* Reduction never results in a new Funk at the same hierarchy
       level, so we use the quad rope implementations. *)
    let mapi_reduce = QuadRope.mapi_reduce
    let map_reduce  = QuadRope.map_reduce
    let reduce      = QuadRope.reduce
  end


module Test(M : Collection2D) =
  struct
    open Shim

    let sum =
      M.reduce ( +. ) 0.


    let pearsons xs ys =
      let size = fun xs -> M.rows xs * M.cols xs in
      let mean = fun xs -> M.reduce ( +. ) 0. xs /. float (size xs) in
      let x_mean  = mean xs in
      let y_mean  = mean ys in
      let x_err   = M.map (fun x -> x -. x_mean) xs in
      let y_err   = M.map (fun y -> y -. y_mean) ys in
      let x_sqerr = M.map (fun x -> x -. x_mean ** 2.) xs in
      let y_sqerr = M.map (fun y -> y -. y_mean ** 2.) ys in
      (sum (M.zipWith ( *.) x_err y_err)) /. (sqrt (sum x_sqerr) *. sqrt (sum y_sqerr))


    let test_pearsons rows cols =
      let xs = M.init rows cols (fun _ _ -> Random.float 1000. +. 1.) in
      let ys = M.init rows cols (fun _ _ -> Random.float 1000. +. 1.) in
      pearsons xs ys


    let test_vdc n =
      let singleton =
        fun x -> M.init 1 1 (fun _ _ -> x) in
      let next =
        fun i is -> M.hcat is (M.hcat (singleton i) (M.map (( +. ) i) is)) in
      let rec vdc n =
        if n <= 1. then
          singleton 0.5
        else
          let n' = 2. ** -.n in
          next n' (vdc (n -. 1.))
      in
      sum (vdc (float n))
  end


module Test_Array2D = Test(Array2D)
module Test_QR      = Test(QuadRope)
module Test_Funky   = Test(Funky)

open Benchmark

let benchmark_pearsons () =
  let res = latencyN (Int64.of_int 200) [("array2d",   (fun x -> Test_Array2D.test_pearsons x x), 400);
                                         ("quad_rope", (fun x -> Test_QR.test_pearsons x x),      400);
                                         ("funky",     (fun x -> Test_Funky.test_pearsons x x),   400)] in
  tabulate res


let benchmark_vdc () =
  let res = latencyN (Int64.of_int 200) [("array2d",   (fun x -> Test_Array2D.test_vdc x), 20);
                                         ("quad_rope", (fun x -> Test_QR.test_vdc x),      20);
                                         ("funky",     (fun x -> Test_Funky.test_vdc x),   20)] in
  tabulate res


let () =
  print_endline "=== Pearsons ===================";
  benchmark_pearsons ();
  print_endline "=== Van der Corput =============";
  benchmark_vdc ();
