#light "off"
module FStar_UInt
open Prims
open FStar_Pervasives

let max_int : Prims.nat  ->  Prims.int = (fun ( n  :  Prims.nat ) -> ((Prims.pow2 n) - (Prims.parse_int "1")))


let min_int : Prims.nat  ->  Prims.int = (fun ( n  :  Prims.nat ) -> (Prims.parse_int "0"))


let fits : Prims.int  ->  Prims.nat  ->  Prims.bool = (fun ( x  :  Prims.int ) ( n  :  Prims.nat ) -> (((min_int n) <= x) && (x <= (max_int n))))


type size =
unit


type uint_t =
Prims.int


let zero : Prims.nat  ->  uint_t = (fun ( n  :  Prims.nat ) -> (Prims.parse_int "0"))


let pow2_n : Prims.pos  ->  Prims.nat  ->  uint_t = (fun ( n  :  Prims.pos ) ( p  :  Prims.nat ) -> (Prims.pow2 p))


let one : Prims.pos  ->  uint_t = (fun ( n  :  Prims.pos ) -> (Prims.parse_int "1"))


let ones : Prims.nat  ->  uint_t = (fun ( n  :  Prims.nat ) -> (max_int n))


let incr : Prims.nat  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) -> (a + (Prims.parse_int "1")))


let decr : Prims.nat  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) -> (a - (Prims.parse_int "1")))


let incr_underspec : Prims.nat  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) -> (match ((a < (max_int n))) with
| true -> begin
(a + (Prims.parse_int "1"))
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let decr_underspec : Prims.nat  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) -> (match ((a > (min_int n))) with
| true -> begin
(a - (Prims.parse_int "1"))
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let incr_mod : Prims.nat  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) -> ((a + (Prims.parse_int "1")) mod (Prims.pow2 n)))


let decr_mod : Prims.nat  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) -> ((a - (Prims.parse_int "1")) mod (Prims.pow2 n)))


let add : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a + b))


let add_underspec : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (match ((fits (a + b) n)) with
| true -> begin
(a + b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let add_mod : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> ((a + b) mod (Prims.pow2 n)))


let sub : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a - b))


let sub_underspec : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (match ((fits (a - b) n)) with
| true -> begin
(a - b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let sub_mod : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> ((a - b) mod (Prims.pow2 n)))


let mul : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a * b))


let mul_underspec : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (match ((fits (a * b) n)) with
| true -> begin
(a * b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let mul_mod : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> ((a * b) mod (Prims.pow2 n)))


let mul_div : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> ((a * b) / (Prims.pow2 n)))


let div : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a / b))


let div_underspec : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (match ((fits (a / b) n)) with
| true -> begin
(a / b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let udiv : Prims.pos  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a / b))


let mod1 : Prims.nat  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a - ((a / b) * b)))


let eq : Prims.nat  ->  uint_t  ->  uint_t  ->  Prims.bool = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (Prims.op_Equality a b))


let gt : Prims.nat  ->  uint_t  ->  uint_t  ->  Prims.bool = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a > b))


let gte : Prims.nat  ->  uint_t  ->  uint_t  ->  Prims.bool = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a >= b))


let lt : Prims.nat  ->  uint_t  ->  uint_t  ->  Prims.bool = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a < b))


let lte : Prims.nat  ->  uint_t  ->  uint_t  ->  Prims.bool = (fun ( n  :  Prims.nat ) ( a  :  uint_t ) ( b  :  uint_t ) -> (a <= b))


let to_uint_t : Prims.nat  ->  Prims.int  ->  uint_t = (fun ( m  :  Prims.nat ) ( a  :  Prims.int ) -> (a mod (Prims.pow2 m)))


let rec to_vec : Prims.nat  ->  uint_t  ->  FStar_BitVector.bv_t = (fun ( n  :  Prims.nat ) ( num  :  uint_t ) -> (match ((Prims.op_Equality n (Prims.parse_int "0"))) with
| true -> begin
(FStar_Seq_Base.empty ())
end
| uu___ -> begin
(FStar_Seq_Base.append (to_vec (n - (Prims.parse_int "1")) (num / (Prims.parse_int "2"))) (FStar_Seq_Base.create (Prims.parse_int "1") (Prims.op_Equality (num mod (Prims.parse_int "2")) (Prims.parse_int "1"))))
end))


let rec from_vec : Prims.nat  ->  FStar_BitVector.bv_t  ->  uint_t = (fun ( n  :  Prims.nat ) ( vec  :  FStar_BitVector.bv_t ) -> (match ((Prims.op_Equality n (Prims.parse_int "0"))) with
| true -> begin
(Prims.parse_int "0")
end
| uu___ -> begin
(((Prims.parse_int "2") * (from_vec (n - (Prims.parse_int "1")) (FStar_Seq_Base.slice vec (Prims.parse_int "0") (n - (Prims.parse_int "1"))))) + (match ((FStar_Seq_Base.index vec (n - (Prims.parse_int "1")))) with
| true -> begin
(Prims.parse_int "1")
end
| uu___1 -> begin
(Prims.parse_int "0")
end))
end))


let nth : Prims.pos  ->  uint_t  ->  Prims.nat  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( i  :  Prims.nat ) -> (FStar_Seq_Base.index (to_vec n a) i))


let logand : Prims.pos  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( b  :  uint_t ) -> (from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))))


let logxor : Prims.pos  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( b  :  uint_t ) -> (from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))))


let logor : Prims.pos  ->  uint_t  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( b  :  uint_t ) -> (from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))))


let lognot : Prims.pos  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) -> (from_vec n (FStar_BitVector.lognot_vec n (to_vec n a))))


let minus : Prims.pos  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) -> (add_mod n (lognot n a) (Prims.parse_int "1")))


let xor : Prims.bool  ->  Prims.bool  ->  Prims.bool = (fun ( b  :  Prims.bool ) ( b'  :  Prims.bool ) -> (Prims.op_disEquality b b'))


let shift_left : Prims.pos  ->  uint_t  ->  Prims.nat  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( s  :  Prims.nat ) -> (from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)))


let shift_right : Prims.pos  ->  uint_t  ->  Prims.nat  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) ( s  :  Prims.nat ) -> (from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)))


let msb : Prims.pos  ->  uint_t  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) -> (nth n a (Prims.parse_int "0")))


let zero_extend_vec : Prims.pos  ->  FStar_BitVector.bv_t  ->  FStar_BitVector.bv_t = (fun ( n  :  Prims.pos ) ( a  :  FStar_BitVector.bv_t ) -> (FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") false) a))


let one_extend_vec : Prims.pos  ->  FStar_BitVector.bv_t  ->  FStar_BitVector.bv_t = (fun ( n  :  Prims.pos ) ( a  :  FStar_BitVector.bv_t ) -> (FStar_Seq_Base.append (FStar_Seq_Base.create (Prims.parse_int "1") true) a))


let zero_extend : Prims.pos  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) -> (from_vec (n + (Prims.parse_int "1")) (zero_extend_vec n (to_vec n a))))


let one_extend : Prims.pos  ->  uint_t  ->  uint_t = (fun ( n  :  Prims.pos ) ( a  :  uint_t ) -> (from_vec (n + (Prims.parse_int "1")) (one_extend_vec n (to_vec n a))))




