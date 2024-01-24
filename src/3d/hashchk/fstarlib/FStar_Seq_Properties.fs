#light "off"
module FStar_Seq_Properties
open Prims
open FStar_Pervasives

type 'a lseq =
'a FStar_Seq_Base.seq


type indexable =
unit


let head = (fun ( s  :  'a FStar_Seq_Base.seq ) -> (FStar_Seq_Base.index s (Prims.parse_int "0")))


let tail = (fun ( s  :  'a FStar_Seq_Base.seq ) -> (FStar_Seq_Base.slice s (Prims.parse_int "1") (FStar_Seq_Base.length s)))


let last = (fun ( s  :  'a FStar_Seq_Base.seq ) -> (FStar_Seq_Base.index s ((FStar_Seq_Base.length s) - (Prims.parse_int "1"))))


let cons = (fun ( x  :  'a ) ( s  :  'a FStar_Seq_Base.seq ) -> (FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") x) s))


let split = (fun ( s  :  'a FStar_Seq_Base.seq ) ( i  :  Prims.nat ) -> (((FStar_Seq_Base.slice s (Prims.parse_int "0") i)), ((FStar_Seq_Base.slice s i (FStar_Seq_Base.length s)))))


let split_eq = (fun ( s  :  'a FStar_Seq_Base.seq ) ( i  :  Prims.nat ) -> (

let x = (split s i)
in x))


let rec count = (fun ( x  :  'a ) ( s  :  'a FStar_Seq_Base.seq ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length s) (Prims.parse_int "0"))) with
| true -> begin
(Prims.parse_int "0")
end
| uu___ -> begin
(match ((Prims.op_Equality (head s) x)) with
| true -> begin
((Prims.parse_int "1") + (count x (tail s)))
end
| uu___1 -> begin
(count x (tail s))
end)
end))


let mem = (fun ( x  :  'a ) ( l  :  'a FStar_Seq_Base.seq ) -> ((count x l) > (Prims.parse_int "0")))


let rec index_mem = (fun ( x  :  'a ) ( s  :  'a FStar_Seq_Base.seq ) -> (match ((Prims.op_Equality (head s) x)) with
| true -> begin
(Prims.parse_int "0")
end
| uu___ -> begin
((Prims.parse_int "1") + (index_mem x (tail s)))
end))


let swap = (fun ( s  :  'a FStar_Seq_Base.seq ) ( i  :  Prims.nat ) ( j  :  Prims.nat ) -> (FStar_Seq_Base.upd (FStar_Seq_Base.upd s j (FStar_Seq_Base.index s i)) i (FStar_Seq_Base.index s j)))


let rec sorted = (fun ( f  :  'a  ->  'a  ->  Prims.bool ) ( s  :  'a FStar_Seq_Base.seq ) -> (match (((FStar_Seq_Base.length s) <= (Prims.parse_int "1"))) with
| true -> begin
true
end
| uu___ -> begin
(

let hd = (head s)
in ((f hd (FStar_Seq_Base.index s (Prims.parse_int "1"))) && (sorted f (tail s))))
end))


type total_order =
unit


type 'a tot_ord =
'a  ->  'a  ->  Prims.bool


let split_5 = (fun ( s  :  'a FStar_Seq_Base.seq ) ( i  :  Prims.nat ) ( j  :  Prims.nat ) -> (

let frag_lo = (FStar_Seq_Base.slice s (Prims.parse_int "0") i)
in (

let frag_i = (FStar_Seq_Base.slice s i (i + (Prims.parse_int "1")))
in (

let frag_mid = (FStar_Seq_Base.slice s (i + (Prims.parse_int "1")) j)
in (

let frag_j = (FStar_Seq_Base.slice s j (j + (Prims.parse_int "1")))
in (

let frag_hi = (FStar_Seq_Base.slice s (j + (Prims.parse_int "1")) (FStar_Seq_Base.length s))
in (FStar_Seq_Base.upd (FStar_Seq_Base.upd (FStar_Seq_Base.upd (FStar_Seq_Base.upd (FStar_Seq_Base.create (Prims.parse_int "5") frag_lo) (Prims.parse_int "1") frag_i) (Prims.parse_int "2") frag_mid) (Prims.parse_int "3") frag_j) (Prims.parse_int "4") frag_hi)))))))


type permutation =
unit


let splice = (fun ( s1  :  'a FStar_Seq_Base.seq ) ( i  :  Prims.nat ) ( s2  :  'a FStar_Seq_Base.seq ) ( j  :  Prims.nat ) -> (FStar_Seq_Base.append (FStar_Seq_Base.slice s1 (Prims.parse_int "0") i) (FStar_Seq_Base.append (FStar_Seq_Base.slice s2 i j) (FStar_Seq_Base.slice s1 j (FStar_Seq_Base.length s1)))))


let replace_subseq = (fun ( s  :  'a FStar_Seq_Base.seq ) ( i  :  Prims.nat ) ( j  :  Prims.nat ) ( sub  :  'a FStar_Seq_Base.seq ) -> (FStar_Seq_Base.append (FStar_Seq_Base.slice s (Prims.parse_int "0") i) (FStar_Seq_Base.append sub (FStar_Seq_Base.slice s j (FStar_Seq_Base.length s)))))


let snoc = (fun ( s  :  'a FStar_Seq_Base.seq ) ( x  :  'a ) -> (FStar_Seq_Base.append s (FStar_Seq_Base.create (Prims.parse_int "1") x)))


let rec find_l = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a FStar_Seq_Base.seq ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length l) (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu___ -> begin
(match ((f (head l))) with
| true -> begin
FStar_Pervasives_Native.Some ((head l))
end
| uu___1 -> begin
(find_l f (tail l))
end)
end))


let un_snoc = (fun ( s  :  'a FStar_Seq_Base.seq ) -> (

let uu___ = (split s ((FStar_Seq_Base.length s) - (Prims.parse_int "1")))
in (match (uu___) with
| (s', a1) -> begin
((s'), ((FStar_Seq_Base.index a1 (Prims.parse_int "0"))))
end)))


let rec find_r = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a FStar_Seq_Base.seq ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length l) (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu___ -> begin
(

let uu___1 = (un_snoc l)
in (match (uu___1) with
| (prefix, last1) -> begin
(match ((f last1)) with
| true -> begin
FStar_Pervasives_Native.Some (last1)
end
| uu___2 -> begin
(find_r f prefix)
end)
end))
end))


type found =
unit


let rec seq_find_aux = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a FStar_Seq_Base.seq ) ( ctr  :  Prims.nat ) -> (match (ctr) with
| uu___ when (uu___ = (Prims.parse_int "0")) -> begin
FStar_Pervasives_Native.None
end
| uu___ -> begin
(

let i = (ctr - (Prims.parse_int "1"))
in (match ((f (FStar_Seq_Base.index l i))) with
| true -> begin
FStar_Pervasives_Native.Some ((FStar_Seq_Base.index l i))
end
| uu___1 -> begin
(seq_find_aux f l i)
end))
end))


let seq_find = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a FStar_Seq_Base.seq ) -> (seq_find_aux f l (FStar_Seq_Base.length l)))


let for_all = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a FStar_Seq_Base.seq ) -> (FStar_Pervasives_Native.uu___is_None (seq_find (fun ( i  :  'a ) -> (not ((f i)))) l)))


let rec seq_to_list = (fun ( s  :  'a FStar_Seq_Base.seq ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length s) (Prims.parse_int "0"))) with
| true -> begin
[]
end
| uu___ -> begin
((FStar_Seq_Base.index s (Prims.parse_int "0")))::(seq_to_list (FStar_Seq_Base.slice s (Prims.parse_int "1") (FStar_Seq_Base.length s)))
end))


let rec seq_of_list = (fun ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
(FStar_Seq_Base.empty ())
end
| (hd)::tl -> begin
(FStar_Seq_Base.op_At_Bar (FStar_Seq_Base.create (Prims.parse_int "1") hd) (seq_of_list tl))
end))


type createL_post =
unit


let createL = (fun ( l  :  'a Prims.list ) -> (

let s = (seq_of_list l)
in s))


type contains =
unit


type suffix_of =
unit


let of_list = (fun ( l  :  'a Prims.list ) -> (seq_of_list l))


type explode_and =
obj


type pointwise_and =
obj


let sortWith = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( s  :  'a FStar_Seq_Base.seq ) -> (seq_of_list (FStar_List_Tot_Base.sortWith f (seq_to_list s))))


let sort_lseq = (fun ( n  :  Prims.nat ) ( f  :  'a tot_ord ) ( s  :  'a lseq ) -> (

let s' = (sortWith (FStar_List_Tot_Base.compare_of_bool f) s)
in s'))


let rec foldr = (fun ( f  :  'b  ->  'a  ->  'a ) ( s  :  'b FStar_Seq_Base.seq ) ( init  :  'a ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length s) (Prims.parse_int "0"))) with
| true -> begin
init
end
| uu___ -> begin
(f (head s) (foldr f (tail s) init))
end))


let rec foldr_snoc = (fun ( f  :  'b  ->  'a  ->  'a ) ( s  :  'b FStar_Seq_Base.seq ) ( init  :  'a ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length s) (Prims.parse_int "0"))) with
| true -> begin
init
end
| uu___ -> begin
(

let uu___1 = (un_snoc s)
in (match (uu___1) with
| (s1, last1) -> begin
(f last1 (foldr_snoc f s1 init))
end))
end))


let rec map_seq = (fun ( f  :  'a  ->  'b ) ( s  :  'a FStar_Seq_Base.seq ) -> (match ((Prims.op_Equality (FStar_Seq_Base.length s) (Prims.parse_int "0"))) with
| true -> begin
(FStar_Seq_Base.empty ())
end
| uu___ -> begin
(

let uu___1 = (((head s)), ((tail s)))
in (match (uu___1) with
| (hd, tl) -> begin
(cons (f hd) (map_seq f tl))
end))
end))




