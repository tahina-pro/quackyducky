#light "off"
module FStar_BitVector
open Prims
open FStar_Pervasives

type bv_t =
Prims.bool FStar_Seq_Base.seq


let zero_vec : Prims.pos  ->  bv_t = (fun ( n  :  Prims.pos ) -> (FStar_Seq_Base.create n false))


let elem_vec : Prims.pos  ->  Prims.nat  ->  bv_t = (fun ( n  :  Prims.pos ) ( i  :  Prims.nat ) -> (FStar_Seq_Base.upd (FStar_Seq_Base.create n false) i true))


let ones_vec : Prims.pos  ->  bv_t = (fun ( n  :  Prims.pos ) -> (FStar_Seq_Base.create n true))


let rec logand_vec : Prims.pos  ->  bv_t  ->  bv_t  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) ( b  :  bv_t ) -> (match ((Prims.op_Equality n (Prims.parse_int "1"))) with
| true -> begin
(FStar_Seq_Base.create (Prims.parse_int "1") ((FStar_Seq_Base.index a (Prims.parse_int "0")) && (FStar_Seq_Base.index b (Prims.parse_int "0"))))
end
| uu___ -> begin
(FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") ((FStar_Seq_Base.index a (Prims.parse_int "0")) && (FStar_Seq_Base.index b (Prims.parse_int "0")))) (logand_vec (n - (Prims.parse_int "1")) (FStar_Seq_Base.slice a (Prims.parse_int "1") n) (FStar_Seq_Base.slice b (Prims.parse_int "1") n)))
end))


let rec logxor_vec : Prims.pos  ->  bv_t  ->  bv_t  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) ( b  :  bv_t ) -> (match ((Prims.op_Equality n (Prims.parse_int "1"))) with
| true -> begin
(FStar_Seq_Base.create (Prims.parse_int "1") (Prims.op_disEquality (FStar_Seq_Base.index a (Prims.parse_int "0")) (FStar_Seq_Base.index b (Prims.parse_int "0"))))
end
| uu___ -> begin
(FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") (Prims.op_disEquality (FStar_Seq_Base.index a (Prims.parse_int "0")) (FStar_Seq_Base.index b (Prims.parse_int "0")))) (logxor_vec (n - (Prims.parse_int "1")) (FStar_Seq_Base.slice a (Prims.parse_int "1") n) (FStar_Seq_Base.slice b (Prims.parse_int "1") n)))
end))


let rec logor_vec : Prims.pos  ->  bv_t  ->  bv_t  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) ( b  :  bv_t ) -> (match ((Prims.op_Equality n (Prims.parse_int "1"))) with
| true -> begin
(FStar_Seq_Base.create (Prims.parse_int "1") ((FStar_Seq_Base.index a (Prims.parse_int "0")) || (FStar_Seq_Base.index b (Prims.parse_int "0"))))
end
| uu___ -> begin
(FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") ((FStar_Seq_Base.index a (Prims.parse_int "0")) || (FStar_Seq_Base.index b (Prims.parse_int "0")))) (logor_vec (n - (Prims.parse_int "1")) (FStar_Seq_Base.slice a (Prims.parse_int "1") n) (FStar_Seq_Base.slice b (Prims.parse_int "1") n)))
end))


let rec lognot_vec : Prims.pos  ->  bv_t  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) -> (match ((Prims.op_Equality n (Prims.parse_int "1"))) with
| true -> begin
(FStar_Seq_Base.create (Prims.parse_int "1") (not ((FStar_Seq_Base.index a (Prims.parse_int "0")))))
end
| uu___ -> begin
(FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") (not ((FStar_Seq_Base.index a (Prims.parse_int "0"))))) (lognot_vec (n - (Prims.parse_int "1")) (FStar_Seq_Base.slice a (Prims.parse_int "1") n)))
end))


type is_subset_vec =
unit


type is_superset_vec =
unit


let shift_left_vec : Prims.pos  ->  bv_t  ->  Prims.nat  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) ( s  :  Prims.nat ) -> (match ((s >= n)) with
| true -> begin
(zero_vec n)
end
| uu___ -> begin
(match ((Prims.op_Equality s (Prims.parse_int "0"))) with
| true -> begin
a
end
| uu___1 -> begin
(FStar_Seq_Base.append (FStar_Seq_Base.slice a s n) (zero_vec s))
end)
end))


let shift_right_vec : Prims.pos  ->  bv_t  ->  Prims.nat  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) ( s  :  Prims.nat ) -> (match ((s >= n)) with
| true -> begin
(zero_vec n)
end
| uu___ -> begin
(match ((Prims.op_Equality s (Prims.parse_int "0"))) with
| true -> begin
a
end
| uu___1 -> begin
(FStar_Seq_Base.append (zero_vec s) (FStar_Seq_Base.slice a (Prims.parse_int "0") (n - s)))
end)
end))


let shift_arithmetic_right_vec : Prims.pos  ->  bv_t  ->  Prims.nat  ->  bv_t = (fun ( n  :  Prims.pos ) ( a  :  bv_t ) ( s  :  Prims.nat ) -> (match ((FStar_Seq_Base.index a (Prims.parse_int "0"))) with
| true -> begin
(match ((s >= n)) with
| true -> begin
(ones_vec n)
end
| uu___ -> begin
(match ((Prims.op_Equality s (Prims.parse_int "0"))) with
| true -> begin
a
end
| uu___1 -> begin
(FStar_Seq_Base.append (ones_vec s) (FStar_Seq_Base.slice a (Prims.parse_int "0") (n - s)))
end)
end)
end
| uu___ -> begin
(shift_right_vec n a s)
end))




