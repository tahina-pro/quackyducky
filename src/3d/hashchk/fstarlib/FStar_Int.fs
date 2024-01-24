#light "off"
module FStar_Int
open Prims
open FStar_Pervasives

let max_int : Prims.pos  ->  Prims.int = (fun ( n  :  Prims.pos ) -> ((Prims.pow2 (n - (Prims.parse_int "1"))) - (Prims.parse_int "1")))


let min_int : Prims.pos  ->  Prims.int = (fun ( n  :  Prims.pos ) -> (- ((Prims.pow2 (n - (Prims.parse_int "1"))))))


let fits : Prims.int  ->  Prims.pos  ->  Prims.bool = (fun ( x  :  Prims.int ) ( n  :  Prims.pos ) -> (((min_int n) <= x) && (x <= (max_int n))))


type size =
unit


type int_t =
Prims.int


let op_Slash : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( a  :  Prims.int ) ( b  :  Prims.int ) -> (match ((((a >= (Prims.parse_int "0")) && (b < (Prims.parse_int "0"))) || ((a < (Prims.parse_int "0")) && (b >= (Prims.parse_int "0"))))) with
| true -> begin
(- (((Prims.abs a) / (Prims.abs b))))
end
| uu___ -> begin
((Prims.abs a) / (Prims.abs b))
end))


let op_At_Percent : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( v  :  Prims.int ) ( p  :  Prims.int ) -> (

let m = (v mod p)
in (match ((m >= (op_Slash p (Prims.parse_int "2")))) with
| true -> begin
(m - p)
end
| uu___ -> begin
m
end)))


let zero : Prims.pos  ->  int_t = (fun ( n  :  Prims.pos ) -> (Prims.parse_int "0"))


let pow2_n : Prims.pos  ->  Prims.nat  ->  int_t = (fun ( n  :  Prims.pos ) ( p  :  Prims.nat ) -> (Prims.pow2 p))


let pow2_minus_one : Prims.pos  ->  Prims.nat  ->  int_t = (fun ( n  :  Prims.pos ) ( m  :  Prims.nat ) -> ((Prims.pow2 m) - (Prims.parse_int "1")))


let one : Prims.pos  ->  int_t = (fun ( n  :  Prims.pos ) -> (Prims.parse_int "1"))


let ones : Prims.pos  ->  int_t = (fun ( n  :  Prims.pos ) -> (Prims.parse_int "-1"))


let incr : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> (a + (Prims.parse_int "1")))


let decr : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> (a - (Prims.parse_int "1")))


let incr_underspec : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> (match ((a < (max_int n))) with
| true -> begin
(a + (Prims.parse_int "1"))
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let decr_underspec : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> (match ((a > (min_int n))) with
| true -> begin
(a - (Prims.parse_int "1"))
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let incr_mod : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> ((a + (Prims.parse_int "1")) mod (Prims.pow2 (n - (Prims.parse_int "1")))))


let decr_mod : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> ((a - (Prims.parse_int "1")) mod (Prims.pow2 (n - (Prims.parse_int "1")))))


let add : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a + b))


let add_underspec : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (match ((fits (a + b) n)) with
| true -> begin
(a + b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let add_mod : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (op_At_Percent (a + b) (Prims.pow2 n)))


let sub : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a - b))


let sub_underspec : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (match ((fits (a - b) n)) with
| true -> begin
(a - b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let sub_mod : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (op_At_Percent (a - b) (Prims.pow2 n)))


let mul : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a * b))


let mul_underspec : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (match ((fits (a * b) n)) with
| true -> begin
(a * b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let mul_mod : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (op_At_Percent (a * b) (Prims.pow2 n)))


let div : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (op_Slash a b))


let div_underspec : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (match ((fits (op_Slash a b) n)) with
| true -> begin
(op_Slash a b)
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let udiv : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (op_Slash a b))


let mod1 : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a - ((op_Slash a b) * b)))


let eq : Prims.pos  ->  int_t  ->  int_t  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (Prims.op_Equality a b))


let gt : Prims.pos  ->  int_t  ->  int_t  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a > b))


let gte : Prims.pos  ->  int_t  ->  int_t  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a >= b))


let lt : Prims.pos  ->  int_t  ->  int_t  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a < b))


let lte : Prims.pos  ->  int_t  ->  int_t  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (a <= b))


let to_uint : Prims.pos  ->  int_t  ->  FStar_UInt.uint_t = (fun ( n  :  Prims.pos ) ( x  :  int_t ) -> (match (((Prims.parse_int "0") <= x)) with
| true -> begin
x
end
| uu___ -> begin
(x + (Prims.pow2 n))
end))


let from_uint : Prims.pos  ->  FStar_UInt.uint_t  ->  int_t = (fun ( n  :  Prims.pos ) ( x  :  FStar_UInt.uint_t ) -> (match ((x <= (max_int n))) with
| true -> begin
x
end
| uu___ -> begin
(x - (Prims.pow2 n))
end))


let to_int_t : Prims.pos  ->  Prims.int  ->  int_t = (fun ( m  :  Prims.pos ) ( a  :  Prims.int ) -> (op_At_Percent a (Prims.pow2 m)))


let to_vec : Prims.pos  ->  int_t  ->  FStar_BitVector.bv_t = (fun ( n  :  Prims.pos ) ( num  :  int_t ) -> (FStar_UInt.to_vec n (to_uint n num)))


let from_vec : Prims.pos  ->  FStar_BitVector.bv_t  ->  int_t = (fun ( n  :  Prims.pos ) ( vec  :  FStar_BitVector.bv_t ) -> (

let x = (FStar_UInt.from_vec n vec)
in (match (((max_int n) < x)) with
| true -> begin
(x - (Prims.pow2 n))
end
| uu___ -> begin
x
end)))


let nth : Prims.pos  ->  int_t  ->  Prims.nat  ->  Prims.bool = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( i  :  Prims.nat ) -> (FStar_Seq_Base.index (to_vec n a) i))


let logand : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (from_vec n (FStar_BitVector.logand_vec n (to_vec n a) (to_vec n b))))


let logxor : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (from_vec n (FStar_BitVector.logxor_vec n (to_vec n a) (to_vec n b))))


let logor : Prims.pos  ->  int_t  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( b  :  int_t ) -> (from_vec n (FStar_BitVector.logor_vec n (to_vec n a) (to_vec n b))))


let lognot : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> (from_vec n (FStar_BitVector.lognot_vec n (to_vec n a))))


let minus : Prims.pos  ->  int_t  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) -> (add_mod n (lognot n a) (Prims.parse_int "1")))


let shift_left : Prims.pos  ->  int_t  ->  Prims.nat  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( s  :  Prims.nat ) -> (from_vec n (FStar_BitVector.shift_left_vec n (to_vec n a) s)))


let shift_right : Prims.pos  ->  int_t  ->  Prims.nat  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( s  :  Prims.nat ) -> (from_vec n (FStar_BitVector.shift_right_vec n (to_vec n a) s)))


let shift_arithmetic_right : Prims.pos  ->  int_t  ->  Prims.nat  ->  int_t = (fun ( n  :  Prims.pos ) ( a  :  int_t ) ( s  :  Prims.nat ) -> (from_vec n (FStar_BitVector.shift_arithmetic_right_vec n (to_vec n a) s)))




