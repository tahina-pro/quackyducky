#light "off"
module FStar_Int128
open Prims
open FStar_Pervasives

let n : Prims.int = (Prims.parse_int "128")

type t =
| Mk of FStar_Int.int_t


let uu___is_Mk : t  ->  Prims.bool = (fun ( projectee  :  t ) -> true)


let __proj__Mk__item__v : t  ->  FStar_Int.int_t = (fun ( projectee  :  t ) -> (match (projectee) with
| Mk (v) -> begin
v
end))


let v : t  ->  FStar_Int.int_t = (fun ( x  :  t ) -> (__proj__Mk__item__v x))


let int_to_t : FStar_Int.int_t  ->  t = (fun ( x  :  FStar_Int.int_t ) -> Mk (x))


let zero : t = (int_to_t (Prims.parse_int "0"))


let one : t = (int_to_t (Prims.parse_int "1"))


let add : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> Mk ((FStar_Int.add (Prims.parse_int "128") (v a) (v b))))


let sub : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> Mk ((FStar_Int.sub (Prims.parse_int "128") (v a) (v b))))


let mul : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> Mk ((FStar_Int.mul (Prims.parse_int "128") (v a) (v b))))


let div : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> Mk ((FStar_Int.div (Prims.parse_int "128") (v a) (v b))))


let rem : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> Mk ((FStar_Int.mod1 (Prims.parse_int "128") (v a) (v b))))


let logand : t  ->  t  ->  t = (fun ( x  :  t ) ( y  :  t ) -> Mk ((FStar_Int.logand (Prims.parse_int "128") (v x) (v y))))


let logxor : t  ->  t  ->  t = (fun ( x  :  t ) ( y  :  t ) -> Mk ((FStar_Int.logxor (Prims.parse_int "128") (v x) (v y))))


let logor : t  ->  t  ->  t = (fun ( x  :  t ) ( y  :  t ) -> Mk ((FStar_Int.logor (Prims.parse_int "128") (v x) (v y))))


let lognot : t  ->  t = (fun ( x  :  t ) -> Mk ((FStar_Int.lognot (Prims.parse_int "128") (v x))))


let shift_right : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> Mk ((FStar_Int.shift_right (Prims.parse_int "128") (v a) (FStar_UInt32.v s))))


let shift_left : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> Mk ((FStar_Int.shift_left (Prims.parse_int "128") (v a) (FStar_UInt32.v s))))


let shift_arithmetic_right : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> Mk ((FStar_Int.shift_arithmetic_right (Prims.parse_int "128") (v a) (FStar_UInt32.v s))))


let eq : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> (FStar_Int.eq (Prims.parse_int "128") (v a) (v b)))


let gt : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> (FStar_Int.gt (Prims.parse_int "128") (v a) (v b)))


let gte : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> (FStar_Int.gte (Prims.parse_int "128") (v a) (v b)))


let lt : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> (FStar_Int.lt (Prims.parse_int "128") (v a) (v b)))


let lte : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> (FStar_Int.lte (Prims.parse_int "128") (v a) (v b)))


let op_Plus_Hat : t  ->  t  ->  t = add


let op_Subtraction_Hat : t  ->  t  ->  t = sub


let op_Star_Hat : t  ->  t  ->  t = mul


let op_Slash_Hat : t  ->  t  ->  t = div


let op_Percent_Hat : t  ->  t  ->  t = rem


let op_Hat_Hat : t  ->  t  ->  t = logxor


let op_Amp_Hat : t  ->  t  ->  t = logand


let op_Bar_Hat : t  ->  t  ->  t = logor


let op_Less_Less_Hat : t  ->  FStar_UInt32.t  ->  t = shift_left


let op_Greater_Greater_Hat : t  ->  FStar_UInt32.t  ->  t = shift_right


let op_Greater_Greater_Greater_Hat : t  ->  FStar_UInt32.t  ->  t = shift_arithmetic_right


let op_Equals_Hat : t  ->  t  ->  Prims.bool = eq


let op_Greater_Hat : t  ->  t  ->  Prims.bool = gt


let op_Greater_Equals_Hat : t  ->  t  ->  Prims.bool = gte


let op_Less_Hat : t  ->  t  ->  Prims.bool = lt


let op_Less_Equals_Hat : t  ->  t  ->  Prims.bool = lte


let ct_abs : t  ->  t = (fun ( a  :  t ) -> (

let mask = (shift_arithmetic_right a (FStar_UInt32.uint_to_t (Prims.parse_int "127")))
in (sub (logxor a mask) mask)))


let to_string : t  ->  Prims.string = (fun ( uu___  :  t ) -> (Prims.admit ()))


let of_string : Prims.string  ->  t = (fun ( uu___  :  Prims.string ) -> (Prims.admit ()))


let __int_to_t : Prims.int  ->  t = (fun ( x  :  Prims.int ) -> (int_to_t x))


let mul_wide : FStar_Int64.t  ->  FStar_Int64.t  ->  t = (fun ( a  :  FStar_Int64.t ) ( b  :  FStar_Int64.t ) -> Mk (((FStar_Int64.v a) * (FStar_Int64.v b))))




