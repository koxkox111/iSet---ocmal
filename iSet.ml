(* Zadanie modyfikacja drzew *)
(* Autor Pawel Dec *)
(* Sprawdzajacy: Pawel Zurakowski *)
type t =    (* lewe_poddrzewo; przedzial_wartosci ; prawe_poddrzewo ; glebokosc_drzewa ; wartosc_poddrzewa *)
    | Empty
    | Node of t * (int * int) * t * int * int

let (++) x y = (* x,y > 0 *)
  if x + y < 0 then max_int
  else x + y

let empty = Empty       (* tworzy pusty set *)

let is_empty x = x = Empty      (*  czy set jest pusty *)

let height t =    (* wysokosc set *)
    match t with
    | Node (_, _, _, h,_) -> h
    | Empty -> 0

let range (a, b) =    (* dlugosc [a,b]*)
  if b - a + 1 <= 0 then max_int else b - a + 1

let count t =   (* ile jest wartosci w set*)
  match t with
  |Empty -> 0
  |Node(_,(a,b),_,_,x) -> range (a,b) ++ x

let make l k r = Node (l, k, r, max (height l) (height r) + 1,count l ++ count r)  (* tworzy set *)

let rec find x t =    (* dla danego x znajduje poddrzewo, w ktorym ten x jest - zwraca set*)
  match t with
  |Empty -> t
  |Node(l,(a,b),r,_,_) ->
    if x < a then find x l
    else if b < x then find x r
    else t

let bal l k r =             (* Balansuje drzewo - bez zmian *)
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _,_) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _,_) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _,_) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _,_) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1,count l ++ count r)

let rec add_one (x,y) t =   (* dodaje  (x,y) - zwraca set *)
    match t with 
    |Node(l,(a,b),r,_,_) ->
    if (x < b) then let nl = add_one (x,y) l in  bal nl (a,b) r
      else let nr = add_one (x,y) r in  bal l (a,b) nr
    | Empty -> Node (Empty, (x,y), Empty, 1,0)

let rec join  l (x,y) r =   (* Bez zmian - laczy sety z przedzialem - zwraca set *)
  match (l, r) with
    (Empty, _) -> add_one  (x,y) r
  | (_, Empty) -> add_one  (x,y) l
  | (Node(ll, lv, lr, lh,_), Node(rl, rv, rr, rh,_)) ->
      if lh > rh + 2 then bal ll lv (join  lr (x,y) r) else
      if rh > lh + 2 then bal (join  l (x,y) rl) rv rr else
      make l (x,y) r

let splitLower x t =     (*drzewo elementow mniejszych/wiekszych od x*)
  let rec loop x t = 
    match t with
    | Empty -> Empty
    | Node(l, (a, b), r, _, _)-> 
      if x <= a then loop x l
      else if x > b then join l (a, b) (loop x r)
      else add_one (a, min (x - 1) b) l
  in loop x t 

let splitHiger x t =
  let rec loop x t =
    match t with
    | Empty -> Empty
    | Node(l, (a, b), r, _, _) ->
      if x >= b then loop x r
      else if x < a then join (loop x l) (a, b) r
      else add_one (max a (x + 1), b) r
  in loop x t

let rec min_elt t = match t with      (*minimalny element set -> zwraca int*)
  | Node (Empty, k, _, _,_) -> k
  | Node (l, _, _, _,_) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt t = match t with       (*usuwa min element -> zwraca set *)
  | Node (Empty, _, r, _,_) -> r
  | Node (l, k, r, _,_) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

let merge t1 t2 =   (* laczy dwa sety  - zwraca set*)
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      join t1 k (remove_min_elt t2)

let remove (a,b) t = (* usuwa przedzial [x,y] z setu - zwraca set*)
  let la = splitLower a t and hb = splitHiger b t
  in merge la hb 

let add (x,y) t =   (* doklada (x,y) do seta,w ktorym nie ma sasiadow (x,y) i (x,y)- zwraca set*)
  let l1 = find (if x = min_int then x else x - 1) t and r1 = find (if y = max_int then y else y +1) t in
  let kresl = match l1 with
    |Node(_,(a,b),_,_,_) -> a
    |Empty->x
  and kresr = match r1 with
    |Node(_,(a,b),_,_,_) -> b
    |Empty -> y
  in let newL = splitLower kresl t and newR = splitHiger kresr t in  (* set poprawny*)
    join newL (kresl,kresr) newR;;

let fold f t acc =      (* bez zmian *)
  let rec loop acc t = match t with
    | Empty -> acc
    | Node (l, (a,b), r, _,_) ->
        loop (f (a,b) (loop acc l)) r in
  loop acc t

let below x t =   (*ilosc elementow mniejszych od x w setcie - zwraca int*)
  let rec pom x t acc =
    match t with
    |Empty -> acc
    |Node(l,(a,b),r,_,_) ->
      if a <= x && x <= b then (*x - a + 1 +acc + count l *)
        range(a,x)++acc ++ count l
      else if x < a then
        pom x l acc
      else
        pom x r (range(a,b)++acc ++ count l) (*b-a+1 +acc +count l*)
  in pom x t 0

let mem x t = not ((find x t) = empty)    (* czy dla danego x istnieje poddrzewo, w ktorym on jest - zwraca bool*)

let elements t =      (* posortowana lista przedzialow seta  - zwraca liste par intow*)
  let rec loop acc t = match t with
    |  Empty -> acc
    | Node(l, k, r, _,_) -> loop (k :: loop acc r) l in
  loop [] t

let iter f t =      (* bez zmian *)
  let rec loop t = match t with
    | Empty -> ()
    | Node (l, k, r, _,_) -> loop l; f k; loop r in
  loop t
let split x t =   
  (splitLower x t, mem x t, splitHiger x t)

(*
let t0 = empty;;
let t1 = add (0,40) t0;;
let t2 = add (85,95) t1;;
let t3 = add (210,290) t2;;
let t4 = add (410,490) t3;;
let t5 = add (50,80) t4;;
let t6 = add (300,400) t5;;
let t7 = add (100,200) t6;;
let t8 = add (100,100) t7;;
let t9 = add (min_int,max_int)(remove (min_int,max_int) t7);;

assert(add (41,84) t8 |> add(95,99) |> add(401,4015) |> add(2137420,6969692137) |> elements =  [(0, 200); (210, 290); (300, 4015); (2137420, 6969692137)]);;
assert(elements t7 =  [(0, 40); (50, 80); (85, 95); (100, 200); (210, 290); (300, 400); (410, 490)]);;
assert(elements t8 =  [(0, 40); (50, 80); (85, 95); (100, 200); (210, 290); (300, 400); (410, 490)]);;
assert(elements t9 = [(-4611686018427387904, 4611686018427387903)]);;
assert(height t7 = 3);;
assert(84 = below 100 t7);;
assert(4611686018427387903 = below 0 t9);;
assert(4611686018427387903 = below max_int t9);;
*)