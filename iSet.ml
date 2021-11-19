exception Spisz;;
type t =
    | Empty
    | Node of t * (int * int) * t * int * int

let (++) x y = (* suma lub max int*)
  if x < 0 || y < 0 then x + y
  else  if x = max_int
    || y = max_int
    || x > max_int - y
    || y > max_int - x
    then max_int
  else x + y

let empty = Empty       (* tworzy pusty set *)

let is_empty x = x = Empty      (*  czy set jest pusty *)

let height t =    (* wysokosc set *)
    match t with
    | Node (_, _, _, h,_) -> h
    | Empty -> 0

let range (a, b) =    (* dlugosc [a,b] *)
  if b - a + 1 <= 0 then max_int else b - a + 1

let count t =   (* ile jest liczb set + dlugosc [a,b}] *)
  match t with
  |Empty -> 0
  |Node(_,(a,b),_,_,x) -> range (a,b) ++ x

let make l k r = Node (l, k, r, max (height l) (height r) + 1,count l ++ count r)      (* laczy dwa sety z korzeniem k - zwraca set, k to korzen*)

let rec bal l k r =             (* Balansuje drzewo, nic tu prawie nie zmienialem, na testach wchodzi z dobrym czasem *)
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _,_) ->
        if height ll >= height lr then bal ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _,_) ->
              bal (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _,_) ->
        if height rr >= height rl then bal (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _,_) ->
              bal (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1,count l ++ count r)

let add_one (x,y) t =   (* praktycznie bez zmian - dodaje (x,y) do t, gdzie - zwraca set *)
    match t with 
    | Node (l, (a,b), r, h,_) ->
      if b < x then
        bal t (x,y) empty
      else
        bal empty (x,y) t
    | Empty -> Node (Empty, (x,y), Empty, 1,0)

let rec join  l (x,y) r =   (* praktycznie bez zmian - laczy sety z przedzialem - zwraca set *)
  match (l, r) with
    (Empty, _) -> add_one  (x,y) r
  | (_, Empty) -> add_one  (x,y) l
  | (Node(ll, lv, lr, lh,_), Node(rl, rv, rr, rh,_)) ->
      if lh > rh + 2 then bal ll lv (join  lr (x,y) r) else
      if rh > lh + 2 then bal (join  l (x,y) rl) rv rr else
      make l (x,y) r

let split x t =     (* dzieli set na L,P gdzie L < x, P > x, oraz czy x byl w t - zwraca (set,bool,set)*)
  let rec loop x t = match t with
    |  Empty ->
        (Empty, false, Empty)
    | Node (l, (a,b), r, _,_) ->
        if a<=x && x <= b then
          let k1 = if a = x then l else join l(a,x-1) empty
          and k2 = if b = x then r else join empty(x+1,b) r
          in (k1,true,k2)
        else if x < a then
          let (ll, pres, rl) = loop x l in (ll, pres, join  rl (a,b) r)
        else
          let (lr, pres, rr) = loop x r in (join  l (a,b) lr, pres, rr)
  in
  let setl, pres, setr = loop x t in
    setl, pres, setr



let rec find x t =    (* dla danego x znajduje poddrzewo, w ktorym ten x jest - zwraca set*)
  match t with
  |Empty -> t
  |Node(l,(a,b),r,_,_) ->
    if x < a then find x l
    else if b < x then find x r
    else t

let mem x t = not ((find x t) = empty)    (* czy dla danego x istnieje poddrzewo, w ktorym on jest - zwraca bool*)


let elements t =      (* posortowana lista przedzialow seta  - zwraca liste par intow*)
  let rec loop acc t = match t with
      Empty -> acc
    | Node(l, k, r, _,_) -> loop (k :: loop acc r) l in
  loop [] t

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
      bal t1 k (remove_min_elt t2)

let remove (a,b) t = (* usuwa przedzial [x,y] z setu - zwraca set*)
  let (la,_,_) = split a t and (_,_,hb) = split b t
  in merge la hb 

let fold f t acc =
  let rec loop acc t = match t with
    | Empty -> acc
    | Node (l, (a,b), r, _,_) ->
          loop (f (a,b) (loop acc l)) r in
  loop acc t

let iter f t =
  let rec loop t = match t with
    | Empty -> ()
    | Node (l, k, r, _,_) -> loop l; f k; loop r in
  loop t

let below x t =   (*ilosc elementow mniejszych od x w setcie - zwraca int*)
  let rec pom x t acc =
    match t with
    |Empty -> acc
    |Node(l,(a,b),r,_,_) ->
      if a <= x && x <= b then (*x - a + 1 +acc + count l *)
        if a <> b then
        x++(-(a++1)) ++2++ acc ++ count l
        else
          1++acc++count l
      else if x < a then
        pom x l acc
      else
        pom x r (if a<> b then b++(-(a+1))++2++acc++count l else 1++acc++count l) (*b-a+1 +acc +count l*)
  in pom x t 0


let rec dodaj (x,y) t =     (* Dodaje do setu przedzial [x,y], set wejsciowy musi byc poprawny, tzn. bez [x,y] oraz bez [a,x-1],[y+1,b] - zwraca set *) 
  match t with
  |Empty -> Node(empty,(x,y),empty,1,0)
  |Node(l,(a,b),r,_,_) ->
  if y < a then
    bal (dodaj (x,y) l) (a,b) r
  else
    bal l (a,b) (dodaj (x,y) r)

let add (x,y) t =   (* najpierw  znajduje poprawy set, patrz wyzej, nastepnie dodaje tam (x,y) - zwraca set*)
    let l1 = find (if x = min_int then x else x - 1) t and r1 = find (if y = max_int then y else y +1) t in
    let kresl = match l1 with
    |Node(_,(a,b),_,_,_) -> a
    |Empty->x
    and kresr = match r1 with
    |Node(_,(a,b),_,_,_) -> b
    |Empty -> y
    in let newT =  (remove (kresl,kresr) t) in  (* set poprawny*)
    match newT with
    |Empty -> join empty (kresl,kresr) empty
    |Node(l,(a,b),r,_,_) -> dodaj (kresl,kresr) newT;;
(*
let t1 = Node(empty,(0,40),empty,1,0);;
let t2 = Node(empty,(85,95),empty,1,0);;
let t3 = Node(empty,(210,290),empty,1,0);;
let t4 = Node(empty,(410,490),empty,1,0);;
let t5 = Node(t1,(50,80),t2,2,count t1 + count t2);;
let t6 = Node(t3,(300,400),t4,2,count t3 + count t4);;
let t7 = Node(t5,(100,200),t6,3,count t5 + count t6);;
let t8 = Node(t5,(100,100),t6,3,count t5 + count t6);;
*)
