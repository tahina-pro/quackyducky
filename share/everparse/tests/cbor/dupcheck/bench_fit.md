### A1_wide_int

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive | hash0-canon |
|---|---|---|---|---|---|---|---|---|---|---|
| 16 | 33 | 1 | 16 | 333 ns | 5.7 us | 5.5 us | 424 ns | 535 ns | 520 ns | 1.2 us |
| 64 | 170 | 1 | 64 | 1.3 us | 82.1 us | 85.3 us | 2.9 us | 2.1 us | 1.9 us | 16.6 us |
| 256 | 747 | 1 | 256 | 4.8 us | 1.2 ms | 1.2 ms | 14.7 us | 7.4 us | 8.1 us | 235.7 us |
| 1024 | 3819 | 1 | 1024 | 19.8 us | 20.3 ms | 21.4 ms | 105.3 us | 34.4 us | 34.4 us | 4.5 ms |
| 4096 | 16107 | 1 | 4096 | 79.2 us | 323.3 ms | 318.2 ms | 552.6 us | 128.1 us | 130.8 us | 79.6 ms |
| 16384 | 65259 | 1 | 16384 | 308.2 us | 4.88 s | 4.82 s | 2.5 ms | 569.3 us | 541.4 us | 1.28 s |
| 65536 | 261869 | 1 | 65536 | 1.1 ms | (capped) | (capped) | 11.6 ms | 2.4 ms | 2.5 ms | (capped) |
| 262144 | 1441517 | 1 | 262144 | 6.1 ms | (capped) | (capped) | 62.4 ms | 10.7 ms | 10.7 ms | (capped) |
| 1.04858e+06 | 6160109 | 1 | 1048576 | 21.8 ms | (capped) | (capped) | 296.6 ms | 45.1 ms | 43.5 ms | (capped) |

Empirical exponent (time vs bytes): wf: 0.94, verified-b: 1.80, verified-u: 1.80, sort: 1.10, hash-canon: 0.96, hash-naive: 0.96, hash0-canon: 1.89

Scratch at the largest parameter: sort 8388672 B, hash-canon 46137552 B, hash-naive 46137552 B

### A3_wide_int_8byte

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 161 | 1 | 16 | 347 ns | 6.8 us | 6.8 us | 907 ns | 589 ns | 593 ns |
| 64 | 642 | 1 | 64 | 1.4 us | 97.6 us | 97.8 us | 5.4 us | 2.2 us | 2.0 us |
| 256 | 2563 | 1 | 256 | 5.1 us | 1.5 ms | 1.5 ms | 33.6 us | 7.8 us | 8.0 us |
| 1024 | 10243 | 1 | 1024 | 21.8 us | 22.0 ms | 21.7 ms | 154.5 us | 31.5 us | 34.9 us |
| 4096 | 40963 | 1 | 4096 | 83.1 us | 368.2 ms | 353.3 ms | 802.6 us | 129.4 us | 132.4 us |
| 16384 | 163843 | 1 | 16384 | 348.1 us | 5.87 s | 5.82 s | 3.6 ms | 619.4 us | 618.1 us |
| 65536 | 655365 | 1 | 65536 | 1.3 ms | (capped) | (capped) | 17.2 ms | 2.5 ms | 2.6 ms |
| 262144 | 2621445 | 1 | 262144 | 5.1 ms | (capped) | (capped) | 81.1 ms | 9.9 ms | 9.6 ms |
| 1.04858e+06 | 10485765 | 1 | 1048576 | 22.3 ms | (capped) | (capped) | 368.2 ms | 45.9 ms | 45.3 ms |

Empirical exponent (time vs bytes): wf: 1.00, verified-b: 1.97, verified-u: 1.97, sort: 1.14, hash-canon: 1.03, hash-naive: 1.03

Scratch at the largest parameter: sort 8388672 B, hash-canon 46137552 B, hash-naive 46137552 B

### A2_wide_prefix_L256

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive | hash0-canon |
|---|---|---|---|---|---|---|---|---|---|---|
| 16 | 4161 | 1 | 16 | 360 ns | 44.6 us | 47.3 us | 772 ns | 2.1 us | 2.0 us | 3.4 us |
| 64 | 16642 | 1 | 64 | 1.5 us | 784.3 us | 793.3 us | 5.0 us | 8.2 us | 8.3 us | 30.9 us |
| 256 | 66563 | 1 | 256 | 5.2 us | 11.9 ms | 11.6 ms | 28.5 us | 30.6 us | 30.6 us | 402.3 us |
| 1024 | 266243 | 1 | 1024 | 21.1 us | 198.0 ms | 199.5 ms | 174.4 us | 123.7 us | 128.9 us | 6.1 ms |
| 4096 | 1064963 | 1 | 4096 | 86.6 us | 3.05 s | 3.08 s | 1.2 ms | 540.9 us | 510.8 us | 97.3 ms |
| 16384 | 4259843 | 1 | 16384 | 341.2 us | (capped) | (capped) | 5.4 ms | 2.1 ms | 2.0 ms | 1.59 s |
| 65536 | 17039365 | 1 | 65536 | 1.4 ms | (capped) | (capped) | 26.9 ms | 8.8 ms | 8.5 ms | (capped) |

Empirical exponent (time vs bytes): wf: 1.00, verified-b: 2.01, verified-u: 2.00, sort: 1.25, hash-canon: 1.00, hash-naive: 1.00, hash0-canon: 1.90

Scratch at the largest parameter: sort 524352 B, hash-canon 2883792 B, hash-naive 2883792 B

### A4_cose_like_array

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 4033 | 2 | 8 | 3.6 us | 27.8 us | 26.5 us | 2.2 us | 4.1 us | 4.0 us |
| 64 | 16130 | 2 | 8 | 14.4 us | 106.3 us | 111.6 us | 9.5 us | 16.2 us | 15.7 us |
| 256 | 64515 | 2 | 8 | 60.1 us | 428.8 us | 451.4 us | 34.4 us | 63.6 us | 68.4 us |
| 1024 | 258051 | 2 | 8 | 226.9 us | 1.8 ms | 1.7 ms | 141.8 us | 272.8 us | 273.6 us |
| 4096 | 1032195 | 2 | 8 | 922.4 us | 7.0 ms | 7.3 ms | 560.2 us | 1.0 ms | 1.0 ms |
| 16384 | 4128771 | 2 | 8 | 3.7 ms | 29.1 ms | 28.3 ms | 2.3 ms | 4.4 ms | 4.2 ms |
| 65536 | 16515077 | 2 | 8 | 15.1 ms | 111.3 ms | 117.7 ms | 9.3 ms | 16.8 ms | 17.8 ms |
| 262144 | 66060293 | 2 | 8 | 61.1 ms | 459.0 ms | 470.1 ms | 37.0 ms | 64.8 ms | 65.8 ms |

Empirical exponent (time vs bytes): wf: 1.00, verified-b: 1.00, verified-u: 1.01, sort: 1.00, hash-canon: 1.00, hash-naive: 1.00

Scratch at the largest parameter: sort 288 B, hash-canon 856 B, hash-naive 760 B

### A5_map_chain

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 33 | 16 | 1 | 333 ns | 4.1 us | 4.3 us | 232 ns | 565 ns | 526 ns |
| 64 | 129 | 64 | 1 | 1.3 us | 53.5 us | 50.0 us | 775 ns | 2.0 us | 1.9 us |
| 256 | 513 | 256 | 1 | 4.9 us | 735.4 us | 748.9 us | 3.1 us | 7.7 us | 7.9 us |
| 1024 | 2049 | 1024 | 1 | 21.8 us | 12.4 ms | 11.7 ms | 13.3 us | 30.6 us | 31.6 us |
| 4096 | 8193 | 4096 | 1 | 79.8 us | 182.7 ms | 194.0 ms | 55.0 us | 127.7 us | 127.2 us |
| 16384 | 32769 | 16384 | 1 | 319.8 us | 3.04 s | 3.12 s | 258.0 us | 541.1 us | 540.6 us |

Empirical exponent (time vs bytes): wf: 1.00, verified-b: 1.96, verified-u: 1.97, sort: 1.06, hash-canon: 1.02, hash-naive: 1.01

Scratch at the largest parameter: sort 786464 B, hash-canon 2097280 B, hash-naive 1900680 B

### B1_map_dupkey

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 21 | 3 | 2 | 208 ns | 2.1 us (dup) | 2.0 us (dup) | 261 ns (dup) | 1.0 us (dup) | 997 ns (dup) |
| 4 | 37 | 5 | 2 | 394 ns | 10.4 us (dup) | 10.5 us (dup) | 594 ns (dup) | 2.0 us (dup) | 1.8 us (dup) |
| 6 | 53 | 7 | 2 | 516 ns | 39.7 us (dup) | 43.6 us (dup) | 882 ns (dup) | 2.7 us (dup) | 2.9 us (dup) |
| 8 | 69 | 9 | 2 | 713 ns | 163.6 us (dup) | 164.0 us (dup) | 1.4 us (dup) | 3.8 us (dup) | 3.7 us (dup) |
| 10 | 85 | 11 | 2 | 819 ns | 709.6 us (dup) | 718.0 us (dup) | 1.9 us (dup) | 5.0 us (dup) | 5.0 us (dup) |
| 12 | 101 | 13 | 2 | 957 ns | 2.7 ms (dup) | 2.8 ms (dup) | 2.2 us (dup) | 5.9 us (dup) | 6.1 us (dup) |
| 14 | 117 | 15 | 2 | 1.1 us | 10.9 ms (dup) | 11.5 ms (dup) | 3.1 us (dup) | 7.4 us (dup) | 7.5 us (dup) |
| 16 | 133 | 17 | 2 | 1.3 us | 43.3 ms (dup) | 45.7 ms (dup) | 3.5 us (dup) | 8.3 us (dup) | 9.5 us (dup) |
| 18 | 149 | 19 | 2 | 1.6 us | 175.8 ms (dup) | 168.2 ms (dup) | 4.3 us (dup) | 10.5 us (dup) | 10.2 us (dup) |
| 20 | 165 | 21 | 2 | 1.6 us | 726.3 ms (dup) | 704.2 ms (dup) | 5.0 us (dup) | 11.0 us (dup) | 11.8 us (dup) |
| 22 | 181 | 23 | 2 | 1.9 us | (capped) | (capped) | 5.5 us (dup) | 12.6 us (dup) | 13.7 us (dup) |
| 24 | 197 | 25 | 2 | 1.9 us | (capped) | (capped) | 7.0 us (dup) | 14.5 us (dup) | 15.6 us (dup) |
| 26 | 213 | 27 | 2 | 2.1 us | (capped) | (capped) | 7.7 us (dup) | 15.6 us (dup) | 16.8 us (dup) |
| 28 | 229 | 29 | 2 | 2.1 us | (capped) | (capped) | 8.5 us (dup) | 17.0 us (dup) | 19.6 us (dup) |
| 30 | 245 | 31 | 2 | 2.4 us | (capped) | (capped) | 10.0 us (dup) | 19.0 us (dup) | 20.9 us (dup) |
| 32 | 261 | 33 | 2 | 2.7 us | (capped) | (capped) | 11.1 us (dup) | 21.5 us (dup) | 22.4 us (dup) |
| 34 | 277 | 35 | 2 | 2.6 us | (capped) | (capped) | 11.3 us (dup) | 21.8 us (dup) | 25.5 us (dup) |
| 36 | 293 | 37 | 2 | 3.0 us | (capped) | (capped) | 13.4 us (dup) | 25.2 us (dup) | 28.7 us (dup) |
| 38 | 309 | 39 | 2 | 2.9 us | (capped) | (capped) | 13.3 us (dup) | 25.6 us (dup) | 31.2 us (dup) |
| 40 | 325 | 41 | 2 | 3.3 us | (capped) | (capped) | 16.0 us (dup) | 28.0 us (dup) | 31.5 us (dup) |
| 42 | 341 | 43 | 2 | 3.5 us | (capped) | (capped) | 15.9 us (dup) | 28.4 us (dup) | 32.6 us (dup) |
| 44 | 357 | 45 | 2 | 3.4 us | (capped) | (capped) | 18.8 us (dup) | 33.3 us (dup) | 38.0 us (dup) |
| 46 | 373 | 47 | 2 | 3.4 us | (capped) | (capped) | 18.3 us (dup) | 32.7 us (dup) | 38.9 us (dup) |
| 48 | 389 | 49 | 2 | 3.7 us | (capped) | (capped) | 20.6 us (dup) | 34.8 us (dup) | 39.7 us (dup) |
| 50 | 405 | 51 | 2 | 3.8 us | (capped) | (capped) | 22.3 us (dup) | 37.9 us (dup) | 43.7 us (dup) |
| 52 | 421 | 53 | 2 | 4.0 us | (capped) | (capped) | 25.0 us (dup) | 42.3 us (dup) | 48.4 us (dup) |
| 54 | 437 | 55 | 2 | 4.3 us | (capped) | (capped) | 25.9 us (dup) | 40.9 us (dup) | 51.9 us (dup) |
| 56 | 453 | 57 | 2 | 4.2 us | (capped) | (capped) | 26.5 us (dup) | 46.8 us (dup) | 55.6 us (dup) |
| 58 | 469 | 59 | 2 | 4.8 us | (capped) | (capped) | 27.5 us (dup) | 44.8 us (dup) | 53.8 us (dup) |
| 60 | 485 | 61 | 2 | 4.6 us | (capped) | (capped) | 29.9 us (dup) | 50.6 us (dup) | 56.4 us (dup) |
| 62 | 501 | 63 | 2 | 4.7 us | (capped) | (capped) | 31.4 us (dup) | 53.5 us (dup) | 58.4 us (dup) |
| 64 | 517 | 65 | 2 | 4.7 us | (capped) | (capped) | 33.3 us (dup) | 51.6 us (dup) | 67.5 us (dup) |

Empirical exponent (time vs bytes): wf: 0.95, verified-b: 6.19, verified-u: 7.45, sort: 1.64, hash-canon: 1.32, hash-naive: 1.40

Average time ratio per unit of depth parameter (input bytes: x1.05): wf: x1.05, verified-b: x2.03, verified-u: x2.04, sort: x1.08, hash-canon: x1.07, hash-naive: x1.07

Scratch at the largest parameter: sort 4176 B, hash-canon 10024 B, hash-naive 8488 B

### B2_resort_n_m32

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 1201 | 2 | 32 | 11.5 us | 1.5 ms | 1.5 ms | 155.6 us | 37.3 us | 37.3 us |
| 64 | 4842 | 2 | 64 | 44.0 us | 22.6 ms | 22.8 ms | 1.1 ms | 149.9 us | 149.7 us |
| 256 | 19435 | 2 | 256 | 186.7 us | 393.3 ms | 391.9 ms | 6.1 ms | 655.6 us | 630.5 us |
| 1024 | 78571 | 2 | 1024 | 707.6 us | 6.57 s | 6.55 s | 30.0 ms | 2.6 ms | 2.8 ms |
| 4096 | 315115 | 2 | 4096 | 3.0 ms | (capped) | (capped) | 155.3 ms | 10.7 ms | 10.2 ms |
| 16384 | 1261291 | 2 | 16384 | 11.4 ms | (capped) | (capped) | 694.7 ms | 43.1 ms | 41.0 ms |

Empirical exponent (time vs bytes): wf: 1.00, verified-b: 2.01, verified-u: 2.00, sort: 1.20, hash-canon: 1.01, hash-naive: 1.01

Scratch at the largest parameter: sort 393312 B, hash-canon 1114424 B, hash-naive 917816 B

### B2_resort_m_n64

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 4 | 682 | 2 | 64 | 6.4 us | 1.0 ms | 1.1 ms | 68.6 us | 24.6 us | 24.4 us |
| 16 | 2218 | 2 | 64 | 21.9 us | 7.0 ms | 6.8 ms | 389.3 us | 82.8 us | 83.6 us |
| 64 | 10986 | 2 | 64 | 94.5 us | 80.7 ms | 83.2 ms | 2.8 ms | 322.8 us | 307.4 us |
| 256 | 47914 | 2 | 256 | 345.1 us | 1.38 s | 1.38 s | 15.4 ms | 1.3 ms | 1.3 ms |
| 1024 | 244522 | 2 | 1024 | 1.3 ms | (capped) | (capped) | 89.8 ms | 5.1 ms | 4.7 ms |
| 4096 | 1030954 | 2 | 4096 | 4.7 ms | (capped) | (capped) | 412.4 ms | 20.6 ms | 20.6 ms |
| 16384 | 4176682 | 2 | 16384 | 18.6 ms | (capped) | (capped) | 1.92 s | 80.3 ms | 79.7 ms |

Empirical exponent (time vs bytes): wf: 0.90, verified-b: 1.68, verified-u: 1.67, sort: 1.16, hash-canon: 0.92, hash-naive: 0.91

Scratch at the largest parameter: sort 393312 B, hash-canon 1114424 B, hash-naive 917816 B

### B4_resort_dup_n_m32

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 1201 | 2 | 32 | 11.6 us | 132.8 us (dup) | 120.8 us (dup) | 132.8 us (dup) | 40.0 us (dup) | 42.4 us (dup) |
| 64 | 4842 | 2 | 64 | 42.2 us | 921.7 us (dup) | 911.6 us (dup) | 1.1 ms (dup) | 154.2 us (dup) | 151.9 us (dup) |
| 256 | 19435 | 2 | 256 | 179.1 us | 3.4 ms (dup) | 3.6 ms (dup) | 5.8 ms (dup) | 669.9 us (dup) | 670.4 us (dup) |
| 1024 | 78571 | 2 | 1024 | 766.0 us | 20.4 ms (dup) | 20.5 ms (dup) | 28.4 ms (dup) | 2.6 ms (dup) | 2.5 ms (dup) |
| 4096 | 315115 | 2 | 4096 | 3.0 ms | 82.2 ms (dup) | 84.5 ms (dup) | 149.7 ms (dup) | 10.9 ms (dup) | 10.5 ms (dup) |
| 16384 | 1261291 | 2 | 16384 | 11.9 ms | 403.4 ms (dup) | 403.2 ms (dup) | 672.8 ms (dup) | 40.8 ms (dup) | 42.0 ms (dup) |

Empirical exponent (time vs bytes): wf: 1.00, verified-b: 1.14, verified-u: 1.15, sort: 1.21, hash-canon: 1.00, hash-naive: 1.00

Scratch at the largest parameter: sort 393312 B, hash-canon 1114424 B, hash-naive 917816 B

### B3_nested_resort_m4_n8

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 97 | 2 | 8 | 803 ns | 18.7 us | 19.4 us | 1.8 us | 3.0 us | 3.2 us |
| 2 | 401 | 3 | 8 | 3.9 us | 254.1 us | 254.6 us | 24.1 us | 13.0 us | 14.1 us |
| 3 | 1617 | 4 | 8 | 15.4 us | 2.8 ms | 2.9 ms | 442.1 us | 57.9 us | 57.7 us |
| 4 | 6481 | 5 | 8 | 62.6 us | 31.2 ms | 31.7 ms | 6.0 ms | 218.2 us | 223.5 us |
| 5 | 25937 | 6 | 8 | 242.9 us | 320.9 ms | 321.2 ms | 85.5 ms | 974.2 us | 902.2 us |
| 6 | 103761 | 7 | 8 | 946.0 us | 4.45 s | 4.50 s | 1.08 s | 3.6 ms | 3.6 ms |
| 7 | 415057 | 8 | 8 | 3.8 ms | (capped) | (capped) | (capped) | 15.5 ms | 14.4 ms |
| 8 | 1660241 | 9 | 8 | 14.3 ms | (capped) | (capped) | (capped) | 70.1 ms | 69.3 ms |
| 9 | 6640977 | 10 | 8 | 56.4 ms | (capped) | (capped) | (capped) | 241.5 ms | 244.5 ms |

Empirical exponent (time vs bytes): wf: 0.99, verified-b: 1.76, verified-u: 1.76, sort: 1.92, hash-canon: 1.02, hash-naive: 1.01

Average time ratio per unit of depth parameter (input bytes: x4.02): wf: x4.03, verified-b: x11.89, verified-u: x11.84, sort: x14.37, hash-canon: x4.10, hash-naive: x4.09

Scratch at the largest parameter: hash-canon 3224 B, hash-naive 2360 B

### B6_array_of_maps_key_n64_m16

| param | bytes | D | N | wf | verified-b | verified-u | sort | hash-canon | hash-naive |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 2282 | 2 | 64 | 22.1 us | 7.5 ms | 8.2 ms | 194.4 us | 85.6 us | 84.3 us |
| 4 | 8618 | 2 | 64 | 83.7 us | 79.8 ms | 84.0 ms | 934.6 us | 316.7 us | 334.4 us |
| 16 | 33962 | 2 | 64 | 315.2 us | 374.9 ms | 384.7 ms | 3.8 ms | 1.2 ms | 1.2 ms |
| 64 | 135402 | 2 | 64 | 1.3 ms | 1.54 s | 1.56 s | 14.6 ms | 5.5 ms | 5.4 ms |
| 256 | 540970 | 2 | 64 | 5.5 ms | (capped) | (capped) | 59.5 ms | 20.1 ms | 19.9 ms |
| 1024 | 2162986 | 2 | 64 | 22.4 ms | (capped) | (capped) | 241.0 ms | 85.8 ms | 86.3 ms |
| 4096 | 8651050 | 2 | 64 | 86.1 ms | (capped) | (capped) | 1.01 s | 339.3 ms | 332.6 ms |

Empirical exponent (time vs bytes): wf: 1.01, verified-b: 1.28, verified-u: 1.27, sort: 1.03, hash-canon: 1.01, hash-naive: 1.00

Scratch at the largest parameter: sort 1632 B, hash-canon 4664 B, hash-naive 3896 B

### A6_wide_int_allcollide

| param | bytes | D | N | sort | hash-canon | hash0-canon |
|---|---|---|---|---|---|---|
| 16 | 33 | 1 | 16 | 482 ns | 510 ns | 1.2 us |
| 32 | 74 | 1 | 32 | 1.0 us | 1.1 us | 4.2 us |
| 64 | 170 | 1 | 64 | 2.9 us | 2.1 us | 15.9 us |
| 128 | 362 | 1 | 128 | 7.3 us | 3.8 us | 63.1 us |
| 256 | 747 | 1 | 256 | 15.9 us | 7.5 us | 238.0 us |
| 512 | 1771 | 1 | 512 | 37.8 us | 18.1 us | 1.1 ms |
| 1024 | 3819 | 1 | 1024 | 106.5 us | 33.3 us | 4.4 ms |
| 2048 | 7915 | 1 | 2048 | 246.4 us | 65.7 us | 18.4 ms |
| 4096 | 16107 | 1 | 4096 | 555.5 us | 128.8 us | 81.6 ms |
| 8192 | 32491 | 1 | 8192 | 1.2 ms | 237.9 us | 326.8 ms |
| 16384 | 65259 | 1 | 16384 | 2.5 ms | 569.6 us | 1.27 s |

Empirical exponent (time vs bytes): sort: 1.14, hash-canon: 0.93, hash0-canon: 1.87

Scratch at the largest parameter: sort 131136 B, hash-canon 721104 B, hash0-canon 721104 B

### B5_resort_allcollide_m32

| param | bytes | D | N | sort | hash-canon | hash0-canon |
|---|---|---|---|---|---|---|
| 16 | 1201 | 2 | 32 | 163.4 us | 40.6 us | 412.0 us |
| 32 | 2410 | 2 | 32 | 403.4 us | 75.1 us | 1.5 ms |
| 64 | 4842 | 2 | 64 | 1.1 ms | 165.0 us | 6.4 ms |
| 128 | 9706 | 2 | 128 | 2.5 ms | 307.8 us | 25.6 ms |
| 256 | 19435 | 2 | 256 | 6.5 ms | 661.7 us | 101.8 ms |
| 512 | 39147 | 2 | 512 | 14.0 ms | 1.3 ms | 388.2 ms |
| 1024 | 78571 | 2 | 1024 | 32.7 ms | 2.7 ms | 1.59 s |
| 2048 | 157419 | 2 | 2048 | 70.7 ms | 5.4 ms | (capped) |

Empirical exponent (time vs bytes): sort: 1.25, hash-canon: 1.01, hash0-canon: 1.98

Scratch at the largest parameter: sort 49248 B, hash-canon 139576 B

