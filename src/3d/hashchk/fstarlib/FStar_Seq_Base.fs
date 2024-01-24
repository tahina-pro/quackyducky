#light "off"
module FStar_Seq_Base
open Prims
open FStar_Pervasives
type 'a seq =
| MkSeq of 'a Prims.list


let uu___is_MkSeq = (fun ( projectee  :  'a seq ) -> true)


let __proj__MkSeq__item__l = (fun ( projectee  :  'a seq ) -> (match (projectee) with
| MkSeq (l) -> begin
l
end))


let length = (fun ( s  :  'uuuuu seq ) -> (FStar_List_Tot_Base.length (__proj__MkSeq__item__l s)))


let index = (fun ( s  :  'uuuuu seq ) ( i  :  Prims.nat ) -> (FStar_List_Tot_Base.index (__proj__MkSeq__item__l s) i))


let cons = (fun ( x  :  'a ) ( s  :  'a seq ) -> MkSeq ((x)::(__proj__MkSeq__item__l s)))


let hd = (fun ( s  :  'a seq ) -> (FStar_List_Tot_Base.hd (__proj__MkSeq__item__l s)))


let tl = (fun ( s  :  'a seq ) -> MkSeq ((FStar_List_Tot_Base.tl (__proj__MkSeq__item__l s))))


let rec create = (fun ( len  :  Prims.nat ) ( v  :  'uuuuu ) -> (match ((Prims.op_Equality len (Prims.parse_int "0"))) with
| true -> begin
MkSeq ([])
end
| uu___ -> begin
(cons v (create (len - (Prims.parse_int "1")) v))
end))


let rec init_aux' = (fun ( len  :  Prims.nat ) ( k  :  Prims.nat ) ( contents  :  Prims.nat  ->  'a ) -> (match ((Prims.op_Equality (k + (Prims.parse_int "1")) len)) with
| true -> begin
MkSeq (((contents k))::[])
end
| uu___ -> begin
(cons (contents k) (init_aux' len (k + (Prims.parse_int "1")) contents))
end))


let init_aux = init_aux'


let init = (fun ( len  :  Prims.nat ) ( contents  :  Prims.nat  ->  'uuuuu ) -> (match ((Prims.op_Equality len (Prims.parse_int "0"))) with
| true -> begin
MkSeq ([])
end
| uu___ -> begin
(init_aux len (Prims.parse_int "0") contents)
end))


let empty = (fun ( uu___  :  unit ) -> MkSeq ([]))


let createEmpty = (fun ( uu___  :  unit ) -> (empty ()))


let rec upd' = (fun ( s  :  'a seq ) ( n  :  Prims.nat ) ( v  :  'a ) -> (match ((Prims.op_Equality n (Prims.parse_int "0"))) with
| true -> begin
(cons v (tl s))
end
| uu___ -> begin
(cons (hd s) (upd' (tl s) (n - (Prims.parse_int "1")) v))
end))


let upd = upd'


let append = (fun ( s1  :  'uuuuu seq ) ( s2  :  'uuuuu seq ) -> MkSeq ((FStar_List_Tot_Base.append (__proj__MkSeq__item__l s1) (__proj__MkSeq__item__l s2))))


let op_At_Bar = (fun ( s1  :  'a seq ) ( s2  :  'a seq ) -> (append s1 s2))


let rec slice' = (fun ( s  :  'a seq ) ( i  :  Prims.nat ) ( j  :  Prims.nat ) -> (match ((i > (Prims.parse_int "0"))) with
| true -> begin
(slice' (tl s) (i - (Prims.parse_int "1")) (j - (Prims.parse_int "1")))
end
| uu___ -> begin
(match ((Prims.op_Equality j (Prims.parse_int "0"))) with
| true -> begin
MkSeq ([])
end
| uu___1 -> begin
(cons (hd s) (slice' (tl s) i (j - (Prims.parse_int "1"))))
end)
end))


let slice = slice'


type equal =
unit


let rec eq_i' = (fun ( s1  :  'a seq ) ( s2  :  'a seq ) ( i  :  Prims.nat ) -> (match ((Prims.op_Equality i (length s1))) with
| true -> begin
true
end
| uu___ -> begin
(match ((Prims.op_Equality (index s1 i) (index s2 i))) with
| true -> begin
(eq_i' s1 s2 (i + (Prims.parse_int "1")))
end
| uu___1 -> begin
false
end)
end))


let eq_i = eq_i'


let eq = (fun ( s1  :  'uuuuu seq ) ( s2  :  'uuuuu seq ) -> (match ((Prims.op_Equality (length s1) (length s2))) with
| true -> begin
(eq_i s1 s2 (Prims.parse_int "0"))
end
| uu___ -> begin
false
end))




