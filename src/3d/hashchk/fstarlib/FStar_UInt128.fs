#light "off"
module FStar_UInt128
open Prims
open FStar_Pervasives

type fact1 =
unit


type fact0 =
unit


let constant_time_carry : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt64.t = (fun ( a  :  FStar_UInt64.t ) ( b  :  FStar_UInt64.t ) -> (FStar_UInt64.shift_right (FStar_UInt64.logxor a (FStar_UInt64.logor (FStar_UInt64.logxor a b) (FStar_UInt64.logxor (FStar_UInt64.sub_mod a b) b))) (FStar_UInt32.uint_to_t ((Prims.parse_int "63")))))

type uint128 =
{low : FStar_UInt64.t; high : FStar_UInt64.t}


let __proj__Mkuint128__item__low : uint128  ->  FStar_UInt64.t = (fun ( projectee  :  uint128 ) -> (match (projectee) with
| {low = low; high = high} -> begin
low
end))


let __proj__Mkuint128__item__high : uint128  ->  FStar_UInt64.t = (fun ( projectee  :  uint128 ) -> (match (projectee) with
| {low = low; high = high} -> begin
high
end))


type t =
uint128


let v : t  ->  FStar_UInt.uint_t = (fun ( x  :  t ) -> ((FStar_UInt64.v x.low) + ((FStar_UInt64.v x.high) * (Prims.pow2 (Prims.parse_int "64")))))


let uint_to_t : FStar_UInt.uint_t  ->  t = (fun ( x  :  FStar_UInt.uint_t ) -> {low = (FStar_UInt64.uint_to_t (x mod (Prims.pow2 (Prims.parse_int "64")))); high = (FStar_UInt64.uint_to_t (x / (Prims.pow2 (Prims.parse_int "64"))))})


let carry : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt64.t = (fun ( a  :  FStar_UInt64.t ) ( b  :  FStar_UInt64.t ) -> (constant_time_carry a b))


let add : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.add_mod a.low b.low); high = (FStar_UInt64.add (FStar_UInt64.add a.high b.high) (carry (FStar_UInt64.add_mod a.low b.low) b.low))})


let add_underspec : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.add_mod a.low b.low); high = (FStar_UInt64.add_underspec (FStar_UInt64.add_underspec a.high b.high) (carry (FStar_UInt64.add_mod a.low b.low) b.low))})


let add_mod : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.add_mod a.low b.low); high = (FStar_UInt64.add_mod (FStar_UInt64.add_mod a.high b.high) (carry (FStar_UInt64.add_mod a.low b.low) b.low))})


let sub : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.sub_mod a.low b.low); high = (FStar_UInt64.sub (FStar_UInt64.sub a.high b.high) (carry a.low (FStar_UInt64.sub_mod a.low b.low)))})


let sub_underspec : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.sub_mod a.low b.low); high = (FStar_UInt64.sub_underspec (FStar_UInt64.sub_underspec a.high b.high) (carry a.low (FStar_UInt64.sub_mod a.low b.low)))})


let sub_mod_impl : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.sub_mod a.low b.low); high = (FStar_UInt64.sub_mod (FStar_UInt64.sub_mod a.high b.high) (carry a.low (FStar_UInt64.sub_mod a.low b.low)))})


let sub_mod : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> (sub_mod_impl a b))


let append_uint : Prims.nat  ->  Prims.nat  ->  FStar_UInt.uint_t  ->  FStar_UInt.uint_t  ->  FStar_UInt.uint_t = (fun ( n1  :  Prims.nat ) ( n2  :  Prims.nat ) ( num1  :  FStar_UInt.uint_t ) ( num2  :  FStar_UInt.uint_t ) -> (num1 + (num2 * (Prims.pow2 n1))))


let vec128 : t  ->  FStar_BitVector.bv_t = (fun ( a  :  t ) -> (FStar_UInt.to_vec (Prims.parse_int "128") (v a)))


let vec64 : FStar_UInt64.t  ->  FStar_BitVector.bv_t = (fun ( a  :  FStar_UInt64.t ) -> (FStar_UInt.to_vec (Prims.parse_int "64") (FStar_UInt64.v a)))


let logand : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.logand a.low b.low); high = (FStar_UInt64.logand a.high b.high)})


let logxor : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.logxor a.low b.low); high = (FStar_UInt64.logxor a.high b.high)})


let logor : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.logor a.low b.low); high = (FStar_UInt64.logor a.high b.high)})


let lognot : t  ->  t = (fun ( a  :  t ) -> {low = (FStar_UInt64.lognot a.low); high = (FStar_UInt64.lognot a.high)})


let __uint_to_t : Prims.int  ->  t = (fun ( x  :  Prims.int ) -> (uint_to_t x))


let u32_64 : FStar_UInt32.t = (FStar_UInt32.uint_to_t (Prims.parse_int "64"))


let add_u64_shift_left : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt32.t  ->  FStar_UInt64.t = (fun ( hi  :  FStar_UInt64.t ) ( lo  :  FStar_UInt64.t ) ( s  :  FStar_UInt32.t ) -> (FStar_UInt64.add (FStar_UInt64.shift_left hi s) (FStar_UInt64.shift_right lo (FStar_UInt32.sub u32_64 s))))


let add_u64_shift_left_respec : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt32.t  ->  FStar_UInt64.t = (fun ( hi  :  FStar_UInt64.t ) ( lo  :  FStar_UInt64.t ) ( s  :  FStar_UInt32.t ) -> (add_u64_shift_left hi lo s))


let shift_left_small : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> (match ((FStar_UInt32.eq s (FStar_UInt32.uint_to_t ((Prims.parse_int "0"))))) with
| true -> begin
a
end
| uu___ -> begin
{low = (FStar_UInt64.shift_left a.low s); high = (add_u64_shift_left_respec a.high a.low s)}
end))


let shift_left_large : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> {low = (FStar_UInt64.uint_to_t (Prims.parse_int "0")); high = (FStar_UInt64.shift_left a.low (FStar_UInt32.sub s u32_64))})


let shift_left : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> (match ((FStar_UInt32.lt s u32_64)) with
| true -> begin
(shift_left_small a s)
end
| uu___ -> begin
(shift_left_large a s)
end))


let add_u64_shift_right : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt32.t  ->  FStar_UInt64.t = (fun ( hi  :  FStar_UInt64.t ) ( lo  :  FStar_UInt64.t ) ( s  :  FStar_UInt32.t ) -> (FStar_UInt64.add (FStar_UInt64.shift_right lo s) (FStar_UInt64.shift_left hi (FStar_UInt32.sub u32_64 s))))


let add_u64_shift_right_respec : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt32.t  ->  FStar_UInt64.t = (fun ( hi  :  FStar_UInt64.t ) ( lo  :  FStar_UInt64.t ) ( s  :  FStar_UInt32.t ) -> (add_u64_shift_right hi lo s))


let shift_right_small : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> (match ((FStar_UInt32.eq s (FStar_UInt32.uint_to_t ((Prims.parse_int "0"))))) with
| true -> begin
a
end
| uu___ -> begin
{low = (add_u64_shift_right_respec a.high a.low s); high = (FStar_UInt64.shift_right a.high s)}
end))


let shift_right_large : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> {low = (FStar_UInt64.shift_right a.high (FStar_UInt32.sub s u32_64)); high = (FStar_UInt64.uint_to_t (Prims.parse_int "0"))})


let shift_right : t  ->  FStar_UInt32.t  ->  t = (fun ( a  :  t ) ( s  :  FStar_UInt32.t ) -> (match ((FStar_UInt32.lt s u32_64)) with
| true -> begin
(shift_right_small a s)
end
| uu___ -> begin
(shift_right_large a s)
end))


let eq : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> ((FStar_UInt64.eq a.low b.low) && (FStar_UInt64.eq a.high b.high)))


let gt : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> ((FStar_UInt64.gt a.high b.high) || ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.gt a.low b.low))))


let lt : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> ((FStar_UInt64.lt a.high b.high) || ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.lt a.low b.low))))


let gte : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> ((FStar_UInt64.gt a.high b.high) || ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.gte a.low b.low))))


let lte : t  ->  t  ->  Prims.bool = (fun ( a  :  t ) ( b  :  t ) -> ((FStar_UInt64.lt a.high b.high) || ((FStar_UInt64.eq a.high b.high) && (FStar_UInt64.lte a.low b.low))))


let eq_mask : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.logand (FStar_UInt64.eq_mask a.low b.low) (FStar_UInt64.eq_mask a.high b.high)); high = (FStar_UInt64.logand (FStar_UInt64.eq_mask a.low b.low) (FStar_UInt64.eq_mask a.high b.high))})


let gte_mask : t  ->  t  ->  t = (fun ( a  :  t ) ( b  :  t ) -> {low = (FStar_UInt64.logor (FStar_UInt64.logand (FStar_UInt64.gte_mask a.high b.high) (FStar_UInt64.lognot (FStar_UInt64.eq_mask a.high b.high))) (FStar_UInt64.logand (FStar_UInt64.eq_mask a.high b.high) (FStar_UInt64.gte_mask a.low b.low))); high = (FStar_UInt64.logor (FStar_UInt64.logand (FStar_UInt64.gte_mask a.high b.high) (FStar_UInt64.lognot (FStar_UInt64.eq_mask a.high b.high))) (FStar_UInt64.logand (FStar_UInt64.eq_mask a.high b.high) (FStar_UInt64.gte_mask a.low b.low)))})


let uint64_to_uint128 : FStar_UInt64.t  ->  t = (fun ( a  :  FStar_UInt64.t ) -> {low = a; high = (FStar_UInt64.uint_to_t (Prims.parse_int "0"))})


let uint128_to_uint64 : t  ->  FStar_UInt64.t = (fun ( a  :  t ) -> a.low)


let u64_l32_mask : FStar_UInt64.t = (FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffff"))


let u64_mod_32 : FStar_UInt64.t  ->  FStar_UInt64.t = (fun ( a  :  FStar_UInt64.t ) -> (FStar_UInt64.logand a (FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffff"))))


let u32_32 : FStar_UInt32.t = (FStar_UInt32.uint_to_t (Prims.parse_int "32"))


let u32_combine : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt64.t = (fun ( hi  :  FStar_UInt64.t ) ( lo  :  FStar_UInt64.t ) -> (FStar_UInt64.add lo (FStar_UInt64.shift_left hi u32_32)))


let mul32 : FStar_UInt64.t  ->  FStar_UInt32.t  ->  t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt32.t ) -> {low = (u32_combine (FStar_UInt64.add (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32) (FStar_Int_Cast.uint32_to_uint64 y)) (FStar_UInt64.shift_right (FStar_UInt64.mul (u64_mod_32 x) (FStar_Int_Cast.uint32_to_uint64 y)) u32_32)) (u64_mod_32 (FStar_UInt64.mul (u64_mod_32 x) (FStar_Int_Cast.uint32_to_uint64 y)))); high = (FStar_UInt64.shift_right (FStar_UInt64.add (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32) (FStar_Int_Cast.uint32_to_uint64 y)) (FStar_UInt64.shift_right (FStar_UInt64.mul (u64_mod_32 x) (FStar_Int_Cast.uint32_to_uint64 y)) u32_32)) u32_32)})


let l32 : FStar_UInt.uint_t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt.uint_t ) -> (x mod (Prims.pow2 (Prims.parse_int "32"))))


let h32 : FStar_UInt.uint_t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt.uint_t ) -> (x / (Prims.pow2 (Prims.parse_int "32"))))


let mul32_bound : FStar_UInt.uint_t  ->  FStar_UInt.uint_t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt.uint_t ) ( y  :  FStar_UInt.uint_t ) -> (x * y))


let pll : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (mul32_bound (l32 (FStar_UInt64.v x)) (l32 (FStar_UInt64.v y))))


let plh : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (mul32_bound (l32 (FStar_UInt64.v x)) (h32 (FStar_UInt64.v y))))


let phl : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (mul32_bound (h32 (FStar_UInt64.v x)) (l32 (FStar_UInt64.v y))))


let phh : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (mul32_bound (h32 (FStar_UInt64.v x)) (h32 (FStar_UInt64.v y))))


let pll_l : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (l32 (pll x y)))


let pll_h : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt.uint_t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (h32 (pll x y)))


let mul_wide_low : FStar_UInt64.t  ->  FStar_UInt64.t  ->  Prims.int = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (((((plh x y) + (((phl x y) + (pll_h x y)) mod (Prims.pow2 (Prims.parse_int "32")))) * (Prims.pow2 (Prims.parse_int "32"))) mod (Prims.pow2 (Prims.parse_int "64"))) + (pll_l x y)))


let mul_wide_high : FStar_UInt64.t  ->  FStar_UInt64.t  ->  Prims.int = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> (((phh x y) + (((phl x y) + (pll_h x y)) / (Prims.pow2 (Prims.parse_int "32")))) + (((plh x y) + (((phl x y) + (pll_h x y)) mod (Prims.pow2 (Prims.parse_int "32")))) / (Prims.pow2 (Prims.parse_int "32")))))


let u32_combine' : FStar_UInt64.t  ->  FStar_UInt64.t  ->  FStar_UInt64.t = (fun ( hi  :  FStar_UInt64.t ) ( lo  :  FStar_UInt64.t ) -> (FStar_UInt64.add lo (FStar_UInt64.shift_left hi u32_32)))


let mul_wide : FStar_UInt64.t  ->  FStar_UInt64.t  ->  t = (fun ( x  :  FStar_UInt64.t ) ( y  :  FStar_UInt64.t ) -> {low = (u32_combine' (FStar_UInt64.add (FStar_UInt64.mul (u64_mod_32 x) (FStar_UInt64.shift_right y u32_32)) (u64_mod_32 (FStar_UInt64.add (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32) (u64_mod_32 y)) (FStar_UInt64.shift_right (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y)) u32_32)))) (u64_mod_32 (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y)))); high = (FStar_UInt64.add_mod (FStar_UInt64.add (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32) (FStar_UInt64.shift_right y u32_32)) (FStar_UInt64.shift_right (FStar_UInt64.add (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32) (u64_mod_32 y)) (FStar_UInt64.shift_right (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y)) u32_32)) u32_32)) (FStar_UInt64.shift_right (FStar_UInt64.add (FStar_UInt64.mul (u64_mod_32 x) (FStar_UInt64.shift_right y u32_32)) (u64_mod_32 (FStar_UInt64.add (FStar_UInt64.mul (FStar_UInt64.shift_right x u32_32) (u64_mod_32 y)) (FStar_UInt64.shift_right (FStar_UInt64.mul (u64_mod_32 x) (u64_mod_32 y)) u32_32)))) u32_32))})




