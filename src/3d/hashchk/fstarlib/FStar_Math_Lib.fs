#light "off"
module FStar_Math_Lib
open Prims
open FStar_Pervasives

let rec log_2 : Prims.pos  ->  Prims.nat = (fun ( x  :  Prims.pos ) -> (match ((x >= (Prims.parse_int "2"))) with
| true -> begin
((Prims.parse_int "1") + (log_2 (x / (Prims.parse_int "2"))))
end
| uu___ -> begin
(Prims.parse_int "0")
end))


let rec powx : Prims.int  ->  Prims.nat  ->  Prims.int = (fun ( x  :  Prims.int ) ( n  :  Prims.nat ) -> (match (n) with
| uu___ when (uu___ = (Prims.parse_int "0")) -> begin
(Prims.parse_int "1")
end
| n1 -> begin
(x * (powx x (n1 - (Prims.parse_int "1"))))
end))


let abs : Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) -> (match ((x >= (Prims.parse_int "0"))) with
| true -> begin
x
end
| uu___ -> begin
(- (x))
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) -> (match ((x >= y)) with
| true -> begin
x
end
| uu___ -> begin
y
end))


let min : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) -> (match ((x >= y)) with
| true -> begin
y
end
| uu___ -> begin
x
end))


let div : Prims.int  ->  Prims.pos  ->  Prims.int = (fun ( a  :  Prims.int ) ( b  :  Prims.pos ) -> (match ((a < (Prims.parse_int "0"))) with
| true -> begin
(match ((Prims.op_Equality (a mod b) (Prims.parse_int "0"))) with
| true -> begin
(- ((- ((a / b)))))
end
| uu___ -> begin
((- ((- ((a / b))))) - (Prims.parse_int "1"))
end)
end
| uu___ -> begin
(a / b)
end))


let div_non_eucl : Prims.int  ->  Prims.pos  ->  Prims.int = (fun ( a  :  Prims.int ) ( b  :  Prims.pos ) -> (match ((a < (Prims.parse_int "0"))) with
| true -> begin
((Prims.parse_int "0") - (((Prims.parse_int "0") - a) / b))
end
| uu___ -> begin
(a / b)
end))


let shift_left : Prims.int  ->  Prims.nat  ->  Prims.int = (fun ( v  :  Prims.int ) ( i  :  Prims.nat ) -> (v * (Prims.pow2 i)))


let arithmetic_shift_right : Prims.int  ->  Prims.nat  ->  Prims.int = (fun ( v  :  Prims.int ) ( i  :  Prims.nat ) -> (div v (Prims.pow2 i)))


let signed_modulo : Prims.int  ->  Prims.pos  ->  Prims.int = (fun ( v  :  Prims.int ) ( p  :  Prims.pos ) -> (match ((v >= (Prims.parse_int "0"))) with
| true -> begin
(v mod p)
end
| uu___ -> begin
((Prims.parse_int "0") - (((Prims.parse_int "0") - v) mod p))
end))


let op_Plus_Percent : Prims.int  ->  Prims.pos  ->  Prims.int = (fun ( a  :  Prims.int ) ( p  :  Prims.pos ) -> (signed_modulo a p))




