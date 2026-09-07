import Zcash.Meta.KernelRfl
import Zcash.Snark.ZeroKnowledge.ActionOrderedShapes

/-!
# The exact legacy sort of the Action regions

The checkpoints preserve every region index, selector column, and tie ordering.
Each phase equation is checked by kernel reduction with an arbitrary recursive
callback. The recursive certificates then compose those phase equations. The
root input is independently checked against all 395 certified source shapes.
These are computation certificates; no exported native result is assumed.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner

section

set_option maxRecDepth 4096

private abbrev s0 : RegionShapeSummary := { columns := [.column .advice 0], rowCount := 1 }
private abbrev s1 : RegionShapeSummary := { columns := [.selector 5, .column .advice 0, .column .advice 1], rowCount := 1 }
private abbrev s2 : RegionShapeSummary := { columns := [.selector 6, .column .advice 0, .column .advice 1], rowCount := 1 }
private abbrev s3 : RegionShapeSummary := { columns := [.selector 27, .column .advice 0, .column .advice 1, .column .advice 4, .column .advice 2, .column .advice 3], rowCount := 1 }
private abbrev s4 : RegionShapeSummary := { columns := [.column .advice 6], rowCount := 1 }
private abbrev s5 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 4], rowCount := 3 }
private abbrev s6 : RegionShapeSummary := { columns := [.selector 26, .column .fixed 3, .column .advice 0, .column .advice 2, .column .advice 1, .column .advice 3, .column .advice 4, .column .fixed 12, .selector 25], rowCount := 53 }
private abbrev s7 : RegionShapeSummary := { columns := [.selector 28, .column .advice 4, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3], rowCount := 2 }
private abbrev s8 : RegionShapeSummary := { columns := [.selector 31, .column .advice 5, .column .advice 6, .column .advice 9, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev s9 : RegionShapeSummary := { columns := [.column .advice 7], rowCount := 1 }
private abbrev s10 : RegionShapeSummary := { columns := [.selector 30, .column .fixed 4, .column .advice 5, .column .advice 7, .column .advice 6, .column .advice 8, .column .advice 9, .column .fixed 13, .selector 29], rowCount := 53 }
private abbrev s11 : RegionShapeSummary := { columns := [.selector 32, .column .advice 9, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev s12 : RegionShapeSummary := { columns := [.column .advice 9], rowCount := 1 }
private abbrev s13 : RegionShapeSummary := { columns := [.column .advice 4, .selector 18, .column .fixed 3, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 9, .column .fixed 10, .column .fixed 11, .column .advice 0, .column .advice 1, .column .advice 5, .selector 7, .column .advice 2, .column .advice 3], rowCount := 23 }
private abbrev s14 : RegionShapeSummary := { columns := [.selector 8, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 4, .selector 20], rowCount := 2 }
private abbrev s15 : RegionShapeSummary := { columns := [.selector 19, .column .advice 4, .column .fixed 3, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 9, .column .fixed 10, .column .fixed 11, .column .advice 0, .column .advice 1, .column .advice 5, .selector 7, .column .advice 2, .column .advice 3], rowCount := 85 }
private abbrev s16 : RegionShapeSummary := { columns := [.selector 8, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 4], rowCount := 2 }
private abbrev s17 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev s18 : RegionShapeSummary := { columns := [.selector 24, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 3 }
private abbrev s19 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .selector 22, .column .fixed 5, .column .fixed 6, .column .fixed 7, .selector 23, .column .advice 5, .column .fixed 8, .column .fixed 9, .column .fixed 10], rowCount := 37 }
private abbrev s20 : RegionShapeSummary := { columns := [.selector 1, .column .advice 7, .column .advice 8, .column .advice 6], rowCount := 1 }
private abbrev s21 : RegionShapeSummary := { columns := [.column .advice 4, .selector 18, .column .fixed 3, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 9, .column .fixed 10, .column .fixed 11, .column .advice 0, .column .advice 1, .column .advice 5, .selector 7, .column .advice 2, .column .advice 3], rowCount := 86 }
private abbrev s22 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 3], rowCount := 14 }
private abbrev s23 : RegionShapeSummary := { columns := [.selector 21, .column .advice 6, .column .advice 8, .column .advice 7], rowCount := 3 }
private abbrev s24 : RegionShapeSummary := { columns := [.selector 26, .column .fixed 3, .column .advice 0, .column .advice 2, .column .advice 1, .column .advice 3, .column .advice 4, .column .fixed 12, .selector 25], rowCount := 52 }
private abbrev s25 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 3], rowCount := 15 }
private abbrev s26 : RegionShapeSummary := { columns := [.selector 33, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev s27 : RegionShapeSummary := { columns := [.selector 8, .column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 4, .column .advice 9, .selector 9, .selector 10, .selector 11, .selector 12, .selector 13, .selector 14, .selector 15, .selector 17], rowCount := 137 }
private abbrev s28 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .selector 16], rowCount := 3 }
private abbrev s29 : RegionShapeSummary := { columns := [], rowCount := 0 }
private abbrev s30 : RegionShapeSummary := { columns := [.column .advice 9, .selector 2, .selector 3], rowCount := 26 }
private abbrev s31 : RegionShapeSummary := { columns := [.selector 44, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 2 }
private abbrev s32 : RegionShapeSummary := { columns := [.selector 26, .column .fixed 3, .column .advice 0, .column .advice 2, .column .advice 1, .column .advice 3, .column .advice 4, .column .fixed 12, .selector 25], rowCount := 110 }
private abbrev s33 : RegionShapeSummary := { columns := [.selector 34, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev s34 : RegionShapeSummary := { columns := [.selector 35, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev s35 : RegionShapeSummary := { columns := [.selector 36, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev s36 : RegionShapeSummary := { columns := [.selector 37, .column .advice 6, .column .advice 7], rowCount := 2 }
private abbrev s37 : RegionShapeSummary := { columns := [.selector 38, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev s38 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 39], rowCount := 2 }
private abbrev s39 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 40], rowCount := 2 }
private abbrev s40 : RegionShapeSummary := { columns := [.selector 41, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 1 }
private abbrev s41 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 42], rowCount := 2 }
private abbrev s42 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 43], rowCount := 2 }
private abbrev s43 : RegionShapeSummary := { columns := [.selector 55, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 2 }
private abbrev s44 : RegionShapeSummary := { columns := [.selector 30, .column .fixed 4, .column .advice 5, .column .advice 7, .column .advice 6, .column .advice 8, .column .advice 9, .column .fixed 13, .selector 29], rowCount := 110 }
private abbrev s45 : RegionShapeSummary := { columns := [.selector 45, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev s46 : RegionShapeSummary := { columns := [.selector 46, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 2 }
private abbrev s47 : RegionShapeSummary := { columns := [.selector 47, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev s48 : RegionShapeSummary := { columns := [.selector 48, .column .advice 6, .column .advice 7], rowCount := 2 }
private abbrev s49 : RegionShapeSummary := { columns := [.selector 49, .column .advice 6, .column .advice 7, .column .advice 8], rowCount := 1 }
private abbrev s50 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 50], rowCount := 2 }
private abbrev s51 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 51], rowCount := 2 }
private abbrev s52 : RegionShapeSummary := { columns := [.selector 52, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9], rowCount := 1 }
private abbrev s53 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 53], rowCount := 2 }
private abbrev s54 : RegionShapeSummary := { columns := [.column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 54], rowCount := 2 }
private abbrev s55 : RegionShapeSummary := { columns := [.column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .column .advice 5, .column .advice 6, .column .advice 7, .selector 0], rowCount := 1 }
private abbrev s56 : RegionShapeSummary := { columns := [.column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .column .advice 5, .column .advice 6, .column .advice 7, .column .advice 8, .column .advice 9, .selector 0], rowCount := 4 }
private abbrev r (index : Nat) (summary : RegionShapeSummary) : RegionShape :=
  { index := index, columns := summary.columns, rowCount := summary.rowCount }

private def input0 : Array RegionShape := #[r 302 s29, r 346 s29]

private def output0 : Array RegionShape := #[r 302 s29, r 346 s29]

private def input1 : Array RegionShape := #[r 301 s2, r 347 s2, r 348 s2, r 4 s2, r 3 s2, r 2 s1]

private def output1 : Array RegionShape := #[r 301 s2, r 347 s2, r 348 s2, r 4 s2, r 3 s2, r 2 s1]

private def input2 : Array RegionShape := #[r 5 s0, r 6 s0, r 7 s0, r 364 s9, r 9 s4, r 362 s9, r 360 s9, r 12
    s4, r 13 s4, r 359 s9, r 356 s9, r 354 s9, r 17 s4, r 353 s9, r 350 s9, r 20 s4, r 21 s4, r 349 s0, r 25
    s4, r 2 s1, r 3 s2, r 4 s2, r 317 s4, r 28 s4, r 29 s4, r 315 s4, r 313 s4, r 312 s4, r 33 s4, r 309 s4, r
    307 s4, r 36 s4, r 37 s4, r 306 s4, r 303 s4, r 133 s4, r 41 s4, r 348 s2, r 347 s2, r 301 s2, r 298 s4, r
    44 s4, r 45 s4, r 289 s4, r 287 s4, r 286 s4, r 49 s4, r 283 s4, r 265 s12, r 52 s4, r 53 s4, r 264 s12, r
    261 s9, r 260 s9, r 57 s4, r 257 s9, r 253 s9, r 60 s4, r 61 s4, r 252 s9, r 249 s9, r 245 s9, r 65 s4, r
    1 s0, r 241 s9, r 68 s4, r 69 s4, r 237 s9, r 236 s9, r 233 s9, r 73 s4, r 229 s9, r 228 s9, r 76 s4, r 77
    s4, r 225 s9, r 221 s9, r 220 s9, r 81 s4, r 217 s9, r 213 s9, r 84 s4, r 85 s4, r 212 s9, r 209 s9, r 205
    s9, r 89 s4, r 204 s9, r 201 s9, r 92 s4, r 93 s4, r 197 s9, r 196 s9, r 193 s9, r 97 s4, r 0 s0, r 189
    s9, r 100 s4, r 101 s4, r 188 s9, r 185 s9, r 181 s9, r 105 s4, r 180 s9, r 177 s9, r 108 s4, r 109 s4, r
    173 s9, r 172 s9, r 169 s9, r 113 s4, r 165 s9, r 164 s9, r 116 s4, r 117 s4, r 161 s9, r 157 s9, r 156
    s9, r 121 s4, r 153 s9, r 149 s9, r 124 s4, r 125 s4, r 148 s9, r 145 s9, r 141 s9, r 129 s4, r 140 s9, r
    137 s9, r 132 s4]

private def output2 : Array RegionShape := #[r 25 s4, r 6 s0, r 7 s0, r 364 s9, r 9 s4, r 362 s9, r 360 s9, r
    12 s4, r 13 s4, r 359 s9, r 356 s9, r 354 s9, r 17 s4, r 353 s9, r 350 s9, r 20 s4, r 21 s4, r 349 s0, r
    241 s9, r 132 s4, r 137 s9, r 140 s9, r 317 s4, r 28 s4, r 1 s0, r 315 s4, r 313 s4, r 312 s4, r 33 s4, r
    309 s4, r 307 s4, r 36 s4, r 37 s4, r 306 s4, r 303 s4, r 133 s4, r 41 s4, r 129 s4, r 141 s9, r 145 s9, r
    298 s4, r 44 s4, r 45 s4, r 289 s4, r 287 s4, r 286 s4, r 49 s4, r 283 s4, r 265 s12, r 52 s4, r 53 s4, r
    264 s12, r 261 s9, r 260 s9, r 57 s4, r 257 s9, r 253 s9, r 60 s4, r 61 s4, r 252 s9, r 249 s9, r 245 s9,
    r 65 s4, r 29 s4, r 68 s4, r 5 s0, r 69 s4, r 237 s9, r 236 s9, r 233 s9, r 73 s4, r 229 s9, r 228 s9, r
    76 s4, r 77 s4, r 225 s9, r 221 s9, r 220 s9, r 81 s4, r 217 s9, r 213 s9, r 84 s4, r 85 s4, r 212 s9, r
    209 s9, r 205 s9, r 89 s4, r 204 s9, r 201 s9, r 92 s4, r 93 s4, r 197 s9, r 196 s9, r 193 s9, r 97 s4, r
    0 s0, r 189 s9, r 100 s4, r 101 s4, r 188 s9, r 185 s9, r 181 s9, r 105 s4, r 180 s9, r 177 s9, r 108 s4,
    r 109 s4, r 173 s9, r 172 s9, r 169 s9, r 113 s4, r 165 s9, r 164 s9, r 116 s4, r 117 s4, r 161 s9, r 157
    s9, r 156 s9, r 121 s4, r 153 s9, r 149 s9, r 124 s4, r 125 s4, r 148 s9, r 301 s2, r 347 s2, r 348 s2, r
    4 s2, r 3 s2, r 2 s1]

private def input3 : Array RegionShape := #[r 133 s4, r 1 s0, r 2 s1, r 3 s2, r 4 s2, r 5 s0, r 6 s0, r 7 s0,
    r 364 s9, r 9 s4, r 362 s9, r 360 s9, r 12 s4, r 13 s4, r 359 s9, r 356 s9, r 354 s9, r 17 s4, r 353 s9, r
    350 s9, r 20 s4, r 21 s4, r 349 s0, r 348 s2, r 347 s2, r 25 s4, r 346 s29, r 317 s4, r 28 s4, r 29 s4, r
    315 s4, r 313 s4, r 312 s4, r 33 s4, r 309 s4, r 307 s4, r 36 s4, r 37 s4, r 306 s4, r 303 s4, r 302 s29,
    r 41 s4, r 301 s2, r 298 s4, r 44 s4, r 45 s4, r 289 s4, r 287 s4, r 286 s4, r 49 s4, r 283 s4, r 265 s12,
    r 52 s4, r 53 s4, r 264 s12, r 261 s9, r 260 s9, r 57 s4, r 257 s9, r 253 s9, r 60 s4, r 61 s4, r 252 s9,
    r 249 s9, r 245 s9, r 65 s4, r 244 s9, r 241 s9, r 68 s4, r 69 s4, r 237 s9, r 236 s9, r 233 s9, r 73 s4,
    r 229 s9, r 228 s9, r 76 s4, r 77 s4, r 225 s9, r 221 s9, r 220 s9, r 81 s4, r 217 s9, r 213 s9, r 84 s4,
    r 85 s4, r 212 s9, r 209 s9, r 205 s9, r 89 s4, r 204 s9, r 201 s9, r 92 s4, r 93 s4, r 197 s9, r 196 s9,
    r 193 s9, r 97 s4, r 0 s0, r 189 s9, r 100 s4, r 101 s4, r 188 s9, r 185 s9, r 181 s9, r 105 s4, r 180 s9,
    r 177 s9, r 108 s4, r 109 s4, r 173 s9, r 172 s9, r 169 s9, r 113 s4, r 165 s9, r 164 s9, r 116 s4, r 117
    s4, r 161 s9, r 157 s9, r 156 s9, r 121 s4, r 153 s9, r 149 s9, r 124 s4, r 125 s4, r 148 s9, r 145 s9, r
    141 s9, r 129 s4, r 140 s9, r 137 s9, r 132 s4]

private def output3 : Array RegionShape := #[r 302 s29, r 346 s29, r 244 s9, r 25 s4, r 6 s0, r 7 s0, r 364
    s9, r 9 s4, r 362 s9, r 360 s9, r 12 s4, r 13 s4, r 359 s9, r 356 s9, r 354 s9, r 17 s4, r 353 s9, r 350
    s9, r 20 s4, r 21 s4, r 349 s0, r 241 s9, r 132 s4, r 137 s9, r 140 s9, r 317 s4, r 28 s4, r 1 s0, r 315
    s4, r 313 s4, r 312 s4, r 33 s4, r 309 s4, r 307 s4, r 36 s4, r 37 s4, r 306 s4, r 303 s4, r 133 s4, r 41
    s4, r 129 s4, r 141 s9, r 145 s9, r 298 s4, r 44 s4, r 45 s4, r 289 s4, r 287 s4, r 286 s4, r 49 s4, r 283
    s4, r 265 s12, r 52 s4, r 53 s4, r 264 s12, r 261 s9, r 260 s9, r 57 s4, r 257 s9, r 253 s9, r 60 s4, r 61
    s4, r 252 s9, r 249 s9, r 245 s9, r 65 s4, r 29 s4, r 68 s4, r 5 s0, r 69 s4, r 237 s9, r 236 s9, r 233
    s9, r 73 s4, r 229 s9, r 228 s9, r 76 s4, r 77 s4, r 225 s9, r 221 s9, r 220 s9, r 81 s4, r 217 s9, r 213
    s9, r 84 s4, r 85 s4, r 212 s9, r 209 s9, r 205 s9, r 89 s4, r 204 s9, r 201 s9, r 92 s4, r 93 s4, r 197
    s9, r 196 s9, r 193 s9, r 97 s4, r 0 s0, r 189 s9, r 100 s4, r 101 s4, r 188 s9, r 185 s9, r 181 s9, r 105
    s4, r 180 s9, r 177 s9, r 108 s4, r 109 s4, r 173 s9, r 172 s9, r 169 s9, r 113 s4, r 165 s9, r 164 s9, r
    116 s4, r 117 s4, r 161 s9, r 157 s9, r 156 s9, r 121 s4, r 153 s9, r 149 s9, r 124 s4, r 125 s4, r 148
    s9, r 301 s2, r 347 s2, r 348 s2, r 4 s2, r 3 s2, r 2 s1]

private def input4 : Array RegionShape := #[r 377 s44, r 280 s15, r 375 s15, r 328 s15, r 330 s32, r 297 s27,
    r 268 s15, r 290 s15, r 275 s21]

private def output4 : Array RegionShape := #[r 280 s15, r 375 s15, r 328 s15, r 268 s15, r 290 s15, r 275 s21,
    r 377 s44, r 330 s32, r 297 s27]

private def input5 : Array RegionShape := #[r 206 s10, r 190 s10, r 102 s6, r 86 s6, r 22 s6, r 14 s6, r 94
    s6, r 182 s10, r 110 s6, r 222 s10, r 174 s10, r 198 s10, r 214 s10, r 268 s15, r 78 s6, r 230 s10, r 166
    s10, r 238 s10, r 330 s32, r 328 s15, r 375 s15, r 70 s6, r 377 s44, r 246 s10, r 30 s6, r 62 s6, r 254
    s10, r 262 s10, r 118 s6, r 134 s6, r 38 s6, r 158 s10, r 280 s15, r 150 s10, r 126 s6, r 46 s6, r 297
    s27, r 142 s10, r 290 s15, r 275 s21]

private def output5 : Array RegionShape := #[r 38 s6, r 190 s10, r 102 s6, r 86 s6, r 22 s6, r 14 s6, r 94 s6,
    r 182 s10, r 110 s6, r 222 s10, r 174 s10, r 198 s10, r 214 s10, r 142 s10, r 78 s6, r 230 s10, r 166 s10,
    r 238 s10, r 46 s6, r 126 s6, r 150 s10, r 70 s6, r 158 s10, r 246 s10, r 30 s6, r 62 s6, r 254 s10, r 262
    s10, r 118 s6, r 134 s6, r 206 s10, r 280 s15, r 375 s15, r 328 s15, r 268 s15, r 290 s15, r 275 s21, r
    377 s44, r 330 s32, r 297 s27]

private def input6 : Array RegionShape := #[r 63 s7, r 111 s7, r 175 s11, r 183 s11, r 15 s7, r 103 s7, r 191
    s11, r 71 s7, r 47 s7, r 143 s11, r 95 s7, r 199 s11, r 23 s7, r 207 s11, r 87 s7, r 215 s11, r 127 s7, r
    151 s11, r 223 s11, r 79 s7, r 369 s43, r 231 s11, r 167 s11, r 159 s11, r 263 s11, r 39 s7, r 119 s7, r
    327 s31, r 239 s11, r 135 s7, r 374 s43, r 255 s11, r 322 s31, r 247 s11, r 31 s7]

private def output6 : Array RegionShape := #[r 63 s7, r 111 s7, r 175 s11, r 183 s11, r 15 s7, r 103 s7, r 191
    s11, r 71 s7, r 47 s7, r 143 s11, r 95 s7, r 199 s11, r 23 s7, r 207 s11, r 87 s7, r 215 s11, r 127 s7, r
    151 s11, r 223 s11, r 79 s7, r 369 s43, r 231 s11, r 167 s11, r 159 s11, r 263 s11, r 39 s7, r 119 s7, r
    327 s31, r 239 s11, r 135 s7, r 374 s43, r 255 s11, r 322 s31, r 247 s11, r 31 s7]

private def input7 : Array RegionShape := #[r 380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25]

private def output7 : Array RegionShape := #[r 380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25]

private def input8 : Array RegionShape := #[r 325 s30, r 292 s24, r 372 s30, r 394 s56, r 273 s19, r 367 s30,
    r 266 s13, r 320 s30]

private def output8 : Array RegionShape := #[r 325 s30, r 372 s30, r 367 s30, r 320 s30, r 394 s56, r 266 s13,
    r 273 s19, r 292 s24]

private def input9 : Array RegionShape := #[r 372 s30, r 331 s16, r 378 s16, r 281 s16, r 279 s16, r 269 s16,
    r 320 s30, r 376 s16, r 276 s16, r 367 s30, r 296 s26, r 329 s16, r 325 s30, r 293 s16, r 292 s24, r 291
    s16, r 394 s56, r 273 s19, r 267 s14, r 266 s13, r 270 s16]

private def output9 : Array RegionShape := #[r 296 s26, r 331 s16, r 378 s16, r 281 s16, r 279 s16, r 269 s16,
    r 270 s16, r 376 s16, r 276 s16, r 267 s14, r 291 s16, r 329 s16, r 293 s16, r 325 s30, r 372 s30, r 367
    s30, r 320 s30, r 394 s56, r 266 s13, r 273 s19, r 292 s24]

private def input10 : Array RegionShape := #[r 325 s30, r 381 s25, r 329 s16, r 372 s30, r 331 s16, r 380 s25,
    r 333 s25, r 334 s25, r 378 s16, r 281 s16, r 279 s16, r 269 s16, r 320 s30, r 376 s16, r 276 s16, r 367
    s30, r 296 s26, r 295 s25, r 282 s16, r 293 s16, r 292 s24, r 291 s16, r 394 s56, r 273 s19, r 267 s14, r
    266 s13, r 270 s16]

private def output10 : Array RegionShape := #[r 380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25, r 282
    s16, r 296 s26, r 331 s16, r 378 s16, r 281 s16, r 279 s16, r 269 s16, r 270 s16, r 376 s16, r 276 s16, r
    267 s14, r 291 s16, r 329 s16, r 293 s16, r 325 s30, r 372 s30, r 367 s30, r 320 s30, r 394 s56, r 266
    s13, r 273 s19, r 292 s24]

private def input11 : Array RegionShape := #[r 378 s16, r 282 s16, r 376 s16, r 320 s30, r 321 s22, r 379 s22,
    r 380 s25, r 381 s25, r 325 s30, r 326 s22, r 382 s22, r 373 s22, r 329 s16, r 372 s30, r 331 s16, r 332
    s22, r 333 s25, r 334 s25, r 335 s22, r 281 s16, r 279 s16, r 269 s16, r 368 s22, r 277 s22, r 276 s16, r
    367 s30, r 296 s26, r 295 s25, r 294 s22, r 293 s16, r 292 s24, r 291 s16, r 394 s56, r 273 s19, r 267
    s14, r 266 s13, r 270 s16]

private def output11 : Array RegionShape := #[r 335 s22, r 294 s22, r 277 s22, r 368 s22, r 321 s22, r 379
    s22, r 332 s22, r 373 s22, r 382 s22, r 326 s22, r 380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25, r
    282 s16, r 296 s26, r 331 s16, r 378 s16, r 281 s16, r 279 s16, r 269 s16, r 270 s16, r 376 s16, r 276
    s16, r 267 s14, r 291 s16, r 329 s16, r 293 s16, r 325 s30, r 372 s30, r 367 s30, r 320 s30, r 394 s56, r
    266 s13, r 273 s19, r 292 s24]

private def input12 : Array RegionShape := #[r 367 s30, r 282 s16, r 270 s16, r 266 s13, r 267 s14, r 273 s19,
    r 394 s56, r 71 s7, r 47 s7, r 143 s11, r 291 s16, r 292 s24, r 293 s16, r 294 s22, r 295 s25, r 296 s26,
    r 127 s7, r 151 s11, r 299 s22, r 276 s16, r 277 s22, r 269 s16, r 279 s16, r 159 s11, r 263 s11, r 39 s7,
    r 119 s7, r 281 s16, r 382 s22, r 135 s7, r 381 s25, r 255 s11, r 380 s25, r 379 s22, r 31 s7, r 63 s7, r
    378 s16, r 247 s11, r 376 s16, r 320 s30, r 321 s22, r 322 s31, r 374 s43, r 239 s11, r 325 s30, r 326
    s22, r 327 s31, r 373 s22, r 329 s16, r 372 s30, r 331 s16, r 332 s22, r 333 s25, r 334 s25, r 335 s22, r
    167 s11, r 231 s11, r 369 s43, r 368 s22, r 79 s7, r 223 s11, r 215 s11, r 87 s7, r 207 s11, r 23 s7, r
    199 s11, r 95 s7, r 191 s11, r 103 s7, r 15 s7, r 183 s11, r 175 s11, r 111 s7]

private def output12 : Array RegionShape := #[r 63 s7, r 111 s7, r 175 s11, r 183 s11, r 15 s7, r 103 s7, r
    191 s11, r 71 s7, r 47 s7, r 143 s11, r 95 s7, r 199 s11, r 23 s7, r 207 s11, r 87 s7, r 215 s11, r 127
    s7, r 151 s11, r 223 s11, r 79 s7, r 369 s43, r 231 s11, r 167 s11, r 159 s11, r 263 s11, r 39 s7, r 119
    s7, r 327 s31, r 239 s11, r 135 s7, r 374 s43, r 255 s11, r 322 s31, r 247 s11, r 31 s7, r 299 s22, r 335
    s22, r 294 s22, r 277 s22, r 368 s22, r 321 s22, r 379 s22, r 332 s22, r 373 s22, r 382 s22, r 326 s22, r
    380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25, r 282 s16, r 296 s26, r 331 s16, r 378 s16, r 281
    s16, r 279 s16, r 269 s16, r 270 s16, r 376 s16, r 276 s16, r 267 s14, r 291 s16, r 329 s16, r 293 s16, r
    325 s30, r 372 s30, r 367 s30, r 320 s30, r 394 s56, r 266 s13, r 273 s19, r 292 s24]

private def input13 : Array RegionShape := #[r 281 s16, r 282 s16, r 270 s16, r 266 s13, r 267 s14, r 273 s19,
    r 268 s15, r 275 s21, r 47 s7, r 290 s15, r 291 s16, r 292 s24, r 293 s16, r 294 s22, r 295 s25, r 296
    s26, r 297 s27, r 46 s6, r 299 s22, r 276 s16, r 277 s22, r 269 s16, r 279 s16, r 280 s15, r 263 s11, r 39
    s7, r 38 s6, r 54 s6, r 134 s6, r 135 s7, r 262 s10, r 255 s11, r 254 s10, r 62 s6, r 31 s7, r 63 s7, r 30
    s6, r 247 s11, r 246 s10, r 320 s30, r 321 s22, r 322 s31, r 70 s6, r 239 s11, r 325 s30, r 326 s22, r 327
    s31, r 328 s15, r 329 s16, r 330 s32, r 331 s16, r 332 s22, r 333 s25, r 334 s25, r 335 s22, r 238 s10, r
    231 s11, r 230 s10, r 78 s6, r 79 s7, r 223 s11, r 222 s10, r 215 s11, r 214 s10, r 86 s6, r 87 s7, r 207
    s11, r 206 s10, r 23 s7, r 22 s6, r 94 s6, r 199 s11, r 198 s10, r 95 s7, r 191 s11, r 190 s10, r 102 s6,
    r 103 s7, r 15 s7, r 14 s6, r 183 s11, r 182 s10, r 110 s6, r 175 s11, r 174 s10, r 111 s7, r 367 s30, r
    368 s22, r 369 s43, r 167 s11, r 166 s10, r 372 s30, r 373 s22, r 374 s43, r 375 s15, r 376 s16, r 377
    s44, r 378 s16, r 379 s22, r 380 s25, r 381 s25, r 382 s22, r 118 s6, r 119 s7, r 159 s11, r 158 s10, r
    151 s11, r 150 s10, r 126 s6, r 127 s7, r 143 s11, r 142 s10, r 71 s7, r 394 s56]

private def output13 : Array RegionShape := #[r 63 s7, r 111 s7, r 175 s11, r 183 s11, r 15 s7, r 103 s7, r
    191 s11, r 71 s7, r 47 s7, r 143 s11, r 95 s7, r 199 s11, r 23 s7, r 207 s11, r 87 s7, r 215 s11, r 127
    s7, r 151 s11, r 223 s11, r 79 s7, r 369 s43, r 231 s11, r 167 s11, r 159 s11, r 263 s11, r 39 s7, r 119
    s7, r 327 s31, r 239 s11, r 135 s7, r 374 s43, r 255 s11, r 322 s31, r 247 s11, r 31 s7, r 299 s22, r 335
    s22, r 294 s22, r 277 s22, r 368 s22, r 321 s22, r 379 s22, r 332 s22, r 373 s22, r 382 s22, r 326 s22, r
    380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25, r 282 s16, r 296 s26, r 331 s16, r 378 s16, r 281
    s16, r 279 s16, r 269 s16, r 270 s16, r 376 s16, r 276 s16, r 267 s14, r 291 s16, r 329 s16, r 293 s16, r
    325 s30, r 372 s30, r 367 s30, r 320 s30, r 394 s56, r 266 s13, r 273 s19, r 292 s24, r 54 s6, r 38 s6, r
    190 s10, r 102 s6, r 86 s6, r 22 s6, r 14 s6, r 94 s6, r 182 s10, r 110 s6, r 222 s10, r 174 s10, r 198
    s10, r 214 s10, r 142 s10, r 78 s6, r 230 s10, r 166 s10, r 238 s10, r 46 s6, r 126 s6, r 150 s10, r 70
    s6, r 158 s10, r 246 s10, r 30 s6, r 62 s6, r 254 s10, r 262 s10, r 118 s6, r 134 s6, r 206 s10, r 280
    s15, r 375 s15, r 328 s15, r 268 s15, r 290 s15, r 275 s21, r 377 s44, r 330 s32, r 297 s27]

private def input14 : Array RegionShape := #[r 278 s23, r 388 s50, r 272 s18, r 389 s51, r 391 s53, r 341 s38,
    r 392 s54, r 300 s28, r 345 s42, r 393 s55, r 342 s39]

private def output14 : Array RegionShape := #[r 388 s50, r 389 s51, r 391 s53, r 341 s38, r 392 s54, r 345
    s42, r 393 s55, r 342 s39, r 278 s23, r 272 s18, r 300 s28]

private def input15 : Array RegionShape := #[r 339 s36, r 386 s48, r 390 s52, r 343 s40]

private def output15 : Array RegionShape := #[r 339 s36, r 386 s48, r 390 s52, r 343 s40]

private def input16 : Array RegionShape := #[r 384 s46, r 337 s34, r 383 s45, r 336 s33]

private def output16 : Array RegionShape := #[r 384 s46, r 337 s34, r 383 s45, r 336 s33]

private def input17 : Array RegionShape := #[r 336 s33, r 232 s8, r 40 s3, r 80 s3, r 216 s8, r 72 s3, r 8 s3,
    r 136 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24 s3, r 200 s8, r 96 s3, r 224 s8, r 64 s3, r 192 s8, r
    16 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256 s8, r 112 s3, r 168 s8, r 383 s45, r 160 s8, r 56 s3,
    r 384 s46, r 120 s3, r 152 s8, r 337 s34, r 128 s3, r 144 s8]

private def output17 : Array RegionShape := #[r 16 s3, r 232 s8, r 224 s8, r 80 s3, r 216 s8, r 72 s3, r 8 s3,
    r 192 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24 s3, r 200 s8, r 96 s3, r 40 s3, r 144 s8, r 136 s8, r
    64 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256 s8, r 112 s3, r 168 s8, r 128 s3, r 160 s8, r 56 s3, r
    152 s8, r 120 s3, r 384 s46, r 337 s34, r 383 s45, r 336 s33]

private def input18 : Array RegionShape := #[r 390 s52, r 224 s8, r 337 s34, r 336 s33, r 232 s8, r 40 s3, r
    80 s3, r 216 s8, r 72 s3, r 8 s3, r 136 s8, r 343 s40, r 240 s8, r 339 s36, r 48 s3, r 88 s3, r 208 s8, r
    24 s3, r 200 s8, r 96 s3, r 248 s8, r 64 s3, r 192 s8, r 16 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r
    256 s8, r 112 s3, r 168 s8, r 383 s45, r 160 s8, r 56 s3, r 384 s46, r 120 s3, r 152 s8, r 386 s48, r 128
    s3, r 144 s8]

private def output18 : Array RegionShape := #[r 339 s36, r 386 s48, r 390 s52, r 343 s40, r 248 s8, r 16 s3, r
    232 s8, r 224 s8, r 80 s3, r 216 s8, r 72 s3, r 8 s3, r 192 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24
    s3, r 200 s8, r 96 s3, r 40 s3, r 144 s8, r 136 s8, r 64 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256
    s8, r 112 s3, r 168 s8, r 128 s3, r 160 s8, r 56 s3, r 152 s8, r 120 s3, r 384 s46, r 337 s34, r 383 s45,
    r 336 s33]

private def input19 : Array RegionShape := #[r 339 s36, r 224 s8, r 337 s34, r 336 s33, r 232 s8, r 341 s38, r
    80 s3, r 216 s8, r 72 s3, r 8 s3, r 342 s39, r 343 s40, r 240 s8, r 344 s41, r 345 s42, r 88 s3, r 208 s8,
    r 24 s3, r 200 s8, r 96 s3, r 248 s8, r 64 s3, r 192 s8, r 16 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r
    256 s8, r 112 s3, r 168 s8, r 383 s45, r 160 s8, r 56 s3, r 384 s46, r 120 s3, r 152 s8, r 386 s48, r 388
    s50, r 272 s18, r 389 s51, r 278 s23, r 128 s3, r 144 s8, r 390 s52, r 391 s53, r 48 s3, r 392 s54, r 300
    s28, r 136 s8, r 393 s55, r 40 s3]

private def output19 : Array RegionShape := #[r 339 s36, r 386 s48, r 390 s52, r 343 s40, r 248 s8, r 16 s3, r
    232 s8, r 224 s8, r 80 s3, r 216 s8, r 72 s3, r 8 s3, r 192 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24
    s3, r 200 s8, r 96 s3, r 40 s3, r 144 s8, r 136 s8, r 64 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256
    s8, r 112 s3, r 168 s8, r 128 s3, r 160 s8, r 56 s3, r 152 s8, r 120 s3, r 384 s46, r 337 s34, r 383 s45,
    r 336 s33, r 344 s41, r 388 s50, r 389 s51, r 391 s53, r 341 s38, r 392 s54, r 345 s42, r 393 s55, r 342
    s39, r 278 s23, r 272 s18, r 300 s28]

private def input20 : Array RegionShape := #[r 304 s5, r 393 s55, r 136 s8, r 392 s54, r 138 s5, r 139 s5, r
    131 s5, r 130 s5, r 391 s53, r 390 s52, r 144 s8, r 128 s3, r 146 s5, r 147 s5, r 389 s51, r 388 s50, r
    387 s49, r 386 s48, r 152 s8, r 123 s5, r 154 s5, r 155 s5, r 122 s5, r 120 s3, r 385 s47, r 384 s46, r
    160 s8, r 383 s45, r 162 s5, r 163 s5, r 371 s5, r 115 s5, r 370 s5, r 366 s5, r 168 s8, r 114 s5, r 170
    s5, r 171 s5, r 112 s3, r 365 s5, r 10 s5, r 363 s5, r 176 s8, r 11 s5, r 178 s5, r 179 s5, r 107 s5, r
    106 s5, r 361 s5, r 358 s5, r 184 s8, r 104 s3, r 186 s5, r 187 s5, r 357 s5, r 16 s3, r 355 s5, r 18 s5,
    r 192 s8, r 99 s5, r 194 s5, r 195 s5, r 96 s3, r 19 s5, r 352 s5, r 351 s5, r 200 s8, r 24 s3, r 202 s5,
    r 203 s5, r 91 s5, r 90 s5, r 26 s5, r 27 s5, r 208 s8, r 88 s3, r 210 s5, r 211 s5, r 345 s42, r 344 s41,
    r 343 s40, r 342 s39, r 216 s8, r 83 s5, r 218 s5, r 219 s5, r 82 s5, r 80 s3, r 341 s38, r 340 s37, r 224
    s8, r 339 s36, r 226 s5, r 227 s5, r 338 s35, r 75 s5, r 337 s34, r 336 s33, r 232 s8, r 74 s5, r 234 s5,
    r 235 s5, r 72 s3, r 8 s3, r 324 s5, r 323 s5, r 240 s8, r 319 s5, r 242 s5, r 243 s5, r 67 s5, r 66 s5, r
    318 s5, r 316 s5, r 248 s8, r 64 s3, r 250 s5, r 251 s5, r 314 s5, r 32 s3, r 34 s5, r 311 s5, r 256 s8, r
    59 s5, r 258 s5, r 259 s5, r 58 s5, r 56 s3, r 310 s5, r 35 s5, r 308 s5, r 305 s5, r 271 s17, r 272 s18,
    r 274 s20, r 278 s23, r 51 s5, r 284 s5, r 285 s5, r 50 s5, r 48 s3, r 288 s5, r 300 s28, r 43 s5, r 42
    s5, r 40 s3]

private def output20 : Array RegionShape := #[r 26 s5, r 42 s5, r 43 s5, r 288 s5, r 138 s5, r 139 s5, r 131
    s5, r 130 s5, r 50 s5, r 285 s5, r 284 s5, r 51 s5, r 146 s5, r 147 s5, r 274 s20, r 271 s17, r 387 s49, r
    305 s5, r 308 s5, r 123 s5, r 154 s5, r 155 s5, r 122 s5, r 35 s5, r 385 s47, r 310 s5, r 58 s5, r 259 s5,
    r 162 s5, r 163 s5, r 371 s5, r 115 s5, r 370 s5, r 366 s5, r 258 s5, r 114 s5, r 170 s5, r 171 s5, r 59
    s5, r 365 s5, r 10 s5, r 363 s5, r 311 s5, r 11 s5, r 178 s5, r 179 s5, r 107 s5, r 106 s5, r 361 s5, r
    358 s5, r 34 s5, r 314 s5, r 186 s5, r 187 s5, r 357 s5, r 251 s5, r 355 s5, r 18 s5, r 250 s5, r 99 s5, r
    194 s5, r 195 s5, r 316 s5, r 19 s5, r 352 s5, r 351 s5, r 318 s5, r 66 s5, r 202 s5, r 203 s5, r 91 s5, r
    90 s5, r 304 s5, r 27 s5, r 67 s5, r 243 s5, r 210 s5, r 211 s5, r 242 s5, r 319 s5, r 323 s5, r 324 s5, r
    235 s5, r 83 s5, r 218 s5, r 219 s5, r 82 s5, r 234 s5, r 74 s5, r 340 s37, r 75 s5, r 338 s35, r 226 s5,
    r 227 s5, r 339 s36, r 386 s48, r 390 s52, r 343 s40, r 248 s8, r 16 s3, r 232 s8, r 224 s8, r 80 s3, r
    216 s8, r 72 s3, r 8 s3, r 192 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24 s3, r 200 s8, r 96 s3, r 40
    s3, r 144 s8, r 136 s8, r 64 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256 s8, r 112 s3, r 168 s8, r
    128 s3, r 160 s8, r 56 s3, r 152 s8, r 120 s3, r 384 s46, r 337 s34, r 383 s45, r 336 s33, r 344 s41, r
    388 s50, r 389 s51, r 391 s53, r 341 s38, r 392 s54, r 345 s42, r 393 s55, r 342 s39, r 278 s23, r 272
    s18, r 300 s28]

private def input21 : Array RegionShape := #[r 134 s6, r 135 s7, r 136 s8, r 71 s7, r 138 s5, r 139 s5, r 131
    s5, r 130 s5, r 142 s10, r 143 s11, r 144 s8, r 128 s3, r 146 s5, r 147 s5, r 127 s7, r 126 s6, r 150 s10,
    r 151 s11, r 152 s8, r 123 s5, r 154 s5, r 155 s5, r 122 s5, r 120 s3, r 158 s10, r 159 s11, r 160 s8, r
    119 s7, r 162 s5, r 163 s5, r 118 s6, r 115 s5, r 166 s10, r 167 s11, r 168 s8, r 114 s5, r 170 s5, r 171
    s5, r 112 s3, r 111 s7, r 174 s10, r 175 s11, r 176 s8, r 110 s6, r 178 s5, r 179 s5, r 107 s5, r 106 s5,
    r 182 s10, r 183 s11, r 184 s8, r 104 s3, r 186 s5, r 187 s5, r 103 s7, r 102 s6, r 190 s10, r 191 s11, r
    192 s8, r 99 s5, r 194 s5, r 195 s5, r 96 s3, r 95 s7, r 198 s10, r 199 s11, r 200 s8, r 94 s6, r 202 s5,
    r 203 s5, r 91 s5, r 90 s5, r 206 s10, r 207 s11, r 208 s8, r 88 s3, r 210 s5, r 211 s5, r 87 s7, r 86 s6,
    r 214 s10, r 215 s11, r 216 s8, r 83 s5, r 218 s5, r 219 s5, r 82 s5, r 80 s3, r 222 s10, r 223 s11, r 224
    s8, r 79 s7, r 226 s5, r 227 s5, r 78 s6, r 75 s5, r 230 s10, r 231 s11, r 232 s8, r 74 s5, r 234 s5, r
    235 s5, r 72 s3, r 8 s3, r 238 s10, r 239 s11, r 240 s8, r 70 s6, r 242 s5, r 243 s5, r 67 s5, r 66 s5, r
    246 s10, r 247 s11, r 248 s8, r 64 s3, r 250 s5, r 251 s5, r 63 s7, r 62 s6, r 254 s10, r 255 s11, r 256
    s8, r 59 s5, r 258 s5, r 259 s5, r 58 s5, r 56 s3, r 262 s10, r 263 s11, r 55 s7, r 54 s6, r 266 s13, r
    267 s14, r 268 s15, r 269 s16, r 270 s16, r 271 s17, r 272 s18, r 273 s19, r 274 s20, r 275 s21, r 276
    s16, r 277 s22, r 278 s23, r 279 s16, r 280 s15, r 281 s16, r 282 s16, r 51 s5, r 284 s5, r 285 s5, r 50
    s5, r 48 s3, r 288 s5, r 47 s7, r 290 s15, r 291 s16, r 292 s24, r 293 s16, r 294 s22, r 295 s25, r 296
    s26, r 297 s27, r 46 s6, r 299 s22, r 300 s28, r 43 s5, r 42 s5, r 40 s3, r 304 s5, r 305 s5, r 39 s7, r
    38 s6, r 308 s5, r 35 s5, r 310 s5, r 311 s5, r 34 s5, r 32 s3, r 314 s5, r 31 s7, r 316 s5, r 30 s6, r
    318 s5, r 319 s5, r 320 s30, r 321 s22, r 322 s31, r 323 s5, r 324 s5, r 325 s30, r 326 s22, r 327 s31, r
    328 s15, r 329 s16, r 330 s32, r 331 s16, r 332 s22, r 333 s25, r 334 s25, r 335 s22, r 336 s33, r 337
    s34, r 338 s35, r 339 s36, r 340 s37, r 341 s38, r 342 s39, r 343 s40, r 344 s41, r 345 s42, r 27 s5, r 26
    s5, r 24 s3, r 23 s7, r 22 s6, r 351 s5, r 352 s5, r 19 s5, r 18 s5, r 355 s5, r 16 s3, r 357 s5, r 358
    s5, r 15 s7, r 14 s6, r 361 s5, r 11 s5, r 363 s5, r 10 s5, r 365 s5, r 366 s5, r 367 s30, r 368 s22, r
    369 s43, r 370 s5, r 371 s5, r 372 s30, r 373 s22, r 374 s43, r 375 s15, r 376 s16, r 377 s44, r 378 s16,
    r 379 s22, r 380 s25, r 381 s25, r 382 s22, r 383 s45, r 384 s46, r 385 s47, r 386 s48, r 387 s49, r 388
    s50, r 389 s51, r 390 s52, r 391 s53, r 392 s54, r 393 s55, r 394 s56]

private def output21 : Array RegionShape := #[r 26 s5, r 42 s5, r 43 s5, r 288 s5, r 138 s5, r 139 s5, r 131
    s5, r 130 s5, r 50 s5, r 285 s5, r 284 s5, r 51 s5, r 146 s5, r 147 s5, r 274 s20, r 271 s17, r 387 s49, r
    305 s5, r 308 s5, r 123 s5, r 154 s5, r 155 s5, r 122 s5, r 35 s5, r 385 s47, r 310 s5, r 58 s5, r 259 s5,
    r 162 s5, r 163 s5, r 371 s5, r 115 s5, r 370 s5, r 366 s5, r 258 s5, r 114 s5, r 170 s5, r 171 s5, r 59
    s5, r 365 s5, r 10 s5, r 363 s5, r 311 s5, r 11 s5, r 178 s5, r 179 s5, r 107 s5, r 106 s5, r 361 s5, r
    358 s5, r 34 s5, r 314 s5, r 186 s5, r 187 s5, r 357 s5, r 251 s5, r 355 s5, r 18 s5, r 250 s5, r 99 s5, r
    194 s5, r 195 s5, r 316 s5, r 19 s5, r 352 s5, r 351 s5, r 318 s5, r 66 s5, r 202 s5, r 203 s5, r 91 s5, r
    90 s5, r 304 s5, r 27 s5, r 67 s5, r 243 s5, r 210 s5, r 211 s5, r 242 s5, r 319 s5, r 323 s5, r 324 s5, r
    235 s5, r 83 s5, r 218 s5, r 219 s5, r 82 s5, r 234 s5, r 74 s5, r 340 s37, r 75 s5, r 338 s35, r 226 s5,
    r 227 s5, r 339 s36, r 386 s48, r 390 s52, r 343 s40, r 248 s8, r 16 s3, r 232 s8, r 224 s8, r 80 s3, r
    216 s8, r 72 s3, r 8 s3, r 192 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24 s3, r 200 s8, r 96 s3, r 40
    s3, r 144 s8, r 136 s8, r 64 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256 s8, r 112 s3, r 168 s8, r
    128 s3, r 160 s8, r 56 s3, r 152 s8, r 120 s3, r 384 s46, r 337 s34, r 383 s45, r 336 s33, r 344 s41, r
    388 s50, r 389 s51, r 391 s53, r 341 s38, r 392 s54, r 345 s42, r 393 s55, r 342 s39, r 278 s23, r 272
    s18, r 300 s28, r 55 s7, r 63 s7, r 111 s7, r 175 s11, r 183 s11, r 15 s7, r 103 s7, r 191 s11, r 71 s7, r
    47 s7, r 143 s11, r 95 s7, r 199 s11, r 23 s7, r 207 s11, r 87 s7, r 215 s11, r 127 s7, r 151 s11, r 223
    s11, r 79 s7, r 369 s43, r 231 s11, r 167 s11, r 159 s11, r 263 s11, r 39 s7, r 119 s7, r 327 s31, r 239
    s11, r 135 s7, r 374 s43, r 255 s11, r 322 s31, r 247 s11, r 31 s7, r 299 s22, r 335 s22, r 294 s22, r 277
    s22, r 368 s22, r 321 s22, r 379 s22, r 332 s22, r 373 s22, r 382 s22, r 326 s22, r 380 s25, r 381 s25, r
    295 s25, r 333 s25, r 334 s25, r 282 s16, r 296 s26, r 331 s16, r 378 s16, r 281 s16, r 279 s16, r 269
    s16, r 270 s16, r 376 s16, r 276 s16, r 267 s14, r 291 s16, r 329 s16, r 293 s16, r 325 s30, r 372 s30, r
    367 s30, r 320 s30, r 394 s56, r 266 s13, r 273 s19, r 292 s24, r 54 s6, r 38 s6, r 190 s10, r 102 s6, r
    86 s6, r 22 s6, r 14 s6, r 94 s6, r 182 s10, r 110 s6, r 222 s10, r 174 s10, r 198 s10, r 214 s10, r 142
    s10, r 78 s6, r 230 s10, r 166 s10, r 238 s10, r 46 s6, r 126 s6, r 150 s10, r 70 s6, r 158 s10, r 246
    s10, r 30 s6, r 62 s6, r 254 s10, r 262 s10, r 118 s6, r 134 s6, r 206 s10, r 280 s15, r 375 s15, r 328
    s15, r 268 s15, r 290 s15, r 275 s21, r 377 s44, r 330 s32, r 297 s27]

private def input22 : Array RegionShape := #[r 0 s0, r 1 s0, r 2 s1, r 3 s2, r 4 s2, r 5 s0, r 6 s0, r 7 s0, r
    8 s3, r 9 s4, r 10 s5, r 11 s5, r 12 s4, r 13 s4, r 14 s6, r 15 s7, r 16 s3, r 17 s4, r 18 s5, r 19 s5, r
    20 s4, r 21 s4, r 22 s6, r 23 s7, r 24 s3, r 25 s4, r 26 s5, r 27 s5, r 28 s4, r 29 s4, r 30 s6, r 31 s7,
    r 32 s3, r 33 s4, r 34 s5, r 35 s5, r 36 s4, r 37 s4, r 38 s6, r 39 s7, r 40 s3, r 41 s4, r 42 s5, r 43
    s5, r 44 s4, r 45 s4, r 46 s6, r 47 s7, r 48 s3, r 49 s4, r 50 s5, r 51 s5, r 52 s4, r 53 s4, r 54 s6, r
    55 s7, r 56 s3, r 57 s4, r 58 s5, r 59 s5, r 60 s4, r 61 s4, r 62 s6, r 63 s7, r 64 s3, r 65 s4, r 66 s5,
    r 67 s5, r 68 s4, r 69 s4, r 70 s6, r 71 s7, r 72 s3, r 73 s4, r 74 s5, r 75 s5, r 76 s4, r 77 s4, r 78
    s6, r 79 s7, r 80 s3, r 81 s4, r 82 s5, r 83 s5, r 84 s4, r 85 s4, r 86 s6, r 87 s7, r 88 s3, r 89 s4, r
    90 s5, r 91 s5, r 92 s4, r 93 s4, r 94 s6, r 95 s7, r 96 s3, r 97 s4, r 98 s5, r 99 s5, r 100 s4, r 101
    s4, r 102 s6, r 103 s7, r 104 s3, r 105 s4, r 106 s5, r 107 s5, r 108 s4, r 109 s4, r 110 s6, r 111 s7, r
    112 s3, r 113 s4, r 114 s5, r 115 s5, r 116 s4, r 117 s4, r 118 s6, r 119 s7, r 120 s3, r 121 s4, r 122
    s5, r 123 s5, r 124 s4, r 125 s4, r 126 s6, r 127 s7, r 128 s3, r 129 s4, r 130 s5, r 131 s5, r 132 s4, r
    133 s4, r 134 s6, r 135 s7, r 136 s8, r 137 s9, r 138 s5, r 139 s5, r 140 s9, r 141 s9, r 142 s10, r 143
    s11, r 144 s8, r 145 s9, r 146 s5, r 147 s5, r 148 s9, r 149 s9, r 150 s10, r 151 s11, r 152 s8, r 153 s9,
    r 154 s5, r 155 s5, r 156 s9, r 157 s9, r 158 s10, r 159 s11, r 160 s8, r 161 s9, r 162 s5, r 163 s5, r
    164 s9, r 165 s9, r 166 s10, r 167 s11, r 168 s8, r 169 s9, r 170 s5, r 171 s5, r 172 s9, r 173 s9, r 174
    s10, r 175 s11, r 176 s8, r 177 s9, r 178 s5, r 179 s5, r 180 s9, r 181 s9, r 182 s10, r 183 s11, r 184
    s8, r 185 s9, r 186 s5, r 187 s5, r 188 s9, r 189 s9, r 190 s10, r 191 s11, r 192 s8, r 193 s9, r 194 s5,
    r 195 s5, r 196 s9, r 197 s9, r 198 s10, r 199 s11, r 200 s8, r 201 s9, r 202 s5, r 203 s5, r 204 s9, r
    205 s9, r 206 s10, r 207 s11, r 208 s8, r 209 s9, r 210 s5, r 211 s5, r 212 s9, r 213 s9, r 214 s10, r 215
    s11, r 216 s8, r 217 s9, r 218 s5, r 219 s5, r 220 s9, r 221 s9, r 222 s10, r 223 s11, r 224 s8, r 225 s9,
    r 226 s5, r 227 s5, r 228 s9, r 229 s9, r 230 s10, r 231 s11, r 232 s8, r 233 s9, r 234 s5, r 235 s5, r
    236 s9, r 237 s9, r 238 s10, r 239 s11, r 240 s8, r 241 s9, r 242 s5, r 243 s5, r 244 s9, r 245 s9, r 246
    s10, r 247 s11, r 248 s8, r 249 s9, r 250 s5, r 251 s5, r 252 s9, r 253 s9, r 254 s10, r 255 s11, r 256
    s8, r 257 s9, r 258 s5, r 259 s5, r 260 s9, r 261 s9, r 262 s10, r 263 s11, r 264 s12, r 265 s12, r 266
    s13, r 267 s14, r 268 s15, r 269 s16, r 270 s16, r 271 s17, r 272 s18, r 273 s19, r 274 s20, r 275 s21, r
    276 s16, r 277 s22, r 278 s23, r 279 s16, r 280 s15, r 281 s16, r 282 s16, r 283 s4, r 284 s5, r 285 s5, r
    286 s4, r 287 s4, r 288 s5, r 289 s4, r 290 s15, r 291 s16, r 292 s24, r 293 s16, r 294 s22, r 295 s25, r
    296 s26, r 297 s27, r 298 s4, r 299 s22, r 300 s28, r 301 s2, r 302 s29, r 303 s4, r 304 s5, r 305 s5, r
    306 s4, r 307 s4, r 308 s5, r 309 s4, r 310 s5, r 311 s5, r 312 s4, r 313 s4, r 314 s5, r 315 s4, r 316
    s5, r 317 s4, r 318 s5, r 319 s5, r 320 s30, r 321 s22, r 322 s31, r 323 s5, r 324 s5, r 325 s30, r 326
    s22, r 327 s31, r 328 s15, r 329 s16, r 330 s32, r 331 s16, r 332 s22, r 333 s25, r 334 s25, r 335 s22, r
    336 s33, r 337 s34, r 338 s35, r 339 s36, r 340 s37, r 341 s38, r 342 s39, r 343 s40, r 344 s41, r 345
    s42, r 346 s29, r 347 s2, r 348 s2, r 349 s0, r 350 s9, r 351 s5, r 352 s5, r 353 s9, r 354 s9, r 355 s5,
    r 356 s9, r 357 s5, r 358 s5, r 359 s9, r 360 s9, r 361 s5, r 362 s9, r 363 s5, r 364 s9, r 365 s5, r 366
    s5, r 367 s30, r 368 s22, r 369 s43, r 370 s5, r 371 s5, r 372 s30, r 373 s22, r 374 s43, r 375 s15, r 376
    s16, r 377 s44, r 378 s16, r 379 s22, r 380 s25, r 381 s25, r 382 s22, r 383 s45, r 384 s46, r 385 s47, r
    386 s48, r 387 s49, r 388 s50, r 389 s51, r 390 s52, r 391 s53, r 392 s54, r 393 s55, r 394 s56]

private def output22 : Array RegionShape := #[r 302 s29, r 346 s29, r 244 s9, r 25 s4, r 6 s0, r 7 s0, r 364
    s9, r 9 s4, r 362 s9, r 360 s9, r 12 s4, r 13 s4, r 359 s9, r 356 s9, r 354 s9, r 17 s4, r 353 s9, r 350
    s9, r 20 s4, r 21 s4, r 349 s0, r 241 s9, r 132 s4, r 137 s9, r 140 s9, r 317 s4, r 28 s4, r 1 s0, r 315
    s4, r 313 s4, r 312 s4, r 33 s4, r 309 s4, r 307 s4, r 36 s4, r 37 s4, r 306 s4, r 303 s4, r 133 s4, r 41
    s4, r 129 s4, r 141 s9, r 145 s9, r 298 s4, r 44 s4, r 45 s4, r 289 s4, r 287 s4, r 286 s4, r 49 s4, r 283
    s4, r 265 s12, r 52 s4, r 53 s4, r 264 s12, r 261 s9, r 260 s9, r 57 s4, r 257 s9, r 253 s9, r 60 s4, r 61
    s4, r 252 s9, r 249 s9, r 245 s9, r 65 s4, r 29 s4, r 68 s4, r 5 s0, r 69 s4, r 237 s9, r 236 s9, r 233
    s9, r 73 s4, r 229 s9, r 228 s9, r 76 s4, r 77 s4, r 225 s9, r 221 s9, r 220 s9, r 81 s4, r 217 s9, r 213
    s9, r 84 s4, r 85 s4, r 212 s9, r 209 s9, r 205 s9, r 89 s4, r 204 s9, r 201 s9, r 92 s4, r 93 s4, r 197
    s9, r 196 s9, r 193 s9, r 97 s4, r 0 s0, r 189 s9, r 100 s4, r 101 s4, r 188 s9, r 185 s9, r 181 s9, r 105
    s4, r 180 s9, r 177 s9, r 108 s4, r 109 s4, r 173 s9, r 172 s9, r 169 s9, r 113 s4, r 165 s9, r 164 s9, r
    116 s4, r 117 s4, r 161 s9, r 157 s9, r 156 s9, r 121 s4, r 153 s9, r 149 s9, r 124 s4, r 125 s4, r 148
    s9, r 301 s2, r 347 s2, r 348 s2, r 4 s2, r 3 s2, r 2 s1, r 98 s5, r 26 s5, r 42 s5, r 43 s5, r 288 s5, r
    138 s5, r 139 s5, r 131 s5, r 130 s5, r 50 s5, r 285 s5, r 284 s5, r 51 s5, r 146 s5, r 147 s5, r 274 s20,
    r 271 s17, r 387 s49, r 305 s5, r 308 s5, r 123 s5, r 154 s5, r 155 s5, r 122 s5, r 35 s5, r 385 s47, r
    310 s5, r 58 s5, r 259 s5, r 162 s5, r 163 s5, r 371 s5, r 115 s5, r 370 s5, r 366 s5, r 258 s5, r 114 s5,
    r 170 s5, r 171 s5, r 59 s5, r 365 s5, r 10 s5, r 363 s5, r 311 s5, r 11 s5, r 178 s5, r 179 s5, r 107 s5,
    r 106 s5, r 361 s5, r 358 s5, r 34 s5, r 314 s5, r 186 s5, r 187 s5, r 357 s5, r 251 s5, r 355 s5, r 18
    s5, r 250 s5, r 99 s5, r 194 s5, r 195 s5, r 316 s5, r 19 s5, r 352 s5, r 351 s5, r 318 s5, r 66 s5, r 202
    s5, r 203 s5, r 91 s5, r 90 s5, r 304 s5, r 27 s5, r 67 s5, r 243 s5, r 210 s5, r 211 s5, r 242 s5, r 319
    s5, r 323 s5, r 324 s5, r 235 s5, r 83 s5, r 218 s5, r 219 s5, r 82 s5, r 234 s5, r 74 s5, r 340 s37, r 75
    s5, r 338 s35, r 226 s5, r 227 s5, r 339 s36, r 386 s48, r 390 s52, r 343 s40, r 248 s8, r 16 s3, r 232
    s8, r 224 s8, r 80 s3, r 216 s8, r 72 s3, r 8 s3, r 192 s8, r 240 s8, r 48 s3, r 88 s3, r 208 s8, r 24 s3,
    r 200 s8, r 96 s3, r 40 s3, r 144 s8, r 136 s8, r 64 s3, r 104 s3, r 32 s3, r 184 s8, r 176 s8, r 256 s8,
    r 112 s3, r 168 s8, r 128 s3, r 160 s8, r 56 s3, r 152 s8, r 120 s3, r 384 s46, r 337 s34, r 383 s45, r
    336 s33, r 344 s41, r 388 s50, r 389 s51, r 391 s53, r 341 s38, r 392 s54, r 345 s42, r 393 s55, r 342
    s39, r 278 s23, r 272 s18, r 300 s28, r 55 s7, r 63 s7, r 111 s7, r 175 s11, r 183 s11, r 15 s7, r 103 s7,
    r 191 s11, r 71 s7, r 47 s7, r 143 s11, r 95 s7, r 199 s11, r 23 s7, r 207 s11, r 87 s7, r 215 s11, r 127
    s7, r 151 s11, r 223 s11, r 79 s7, r 369 s43, r 231 s11, r 167 s11, r 159 s11, r 263 s11, r 39 s7, r 119
    s7, r 327 s31, r 239 s11, r 135 s7, r 374 s43, r 255 s11, r 322 s31, r 247 s11, r 31 s7, r 299 s22, r 335
    s22, r 294 s22, r 277 s22, r 368 s22, r 321 s22, r 379 s22, r 332 s22, r 373 s22, r 382 s22, r 326 s22, r
    380 s25, r 381 s25, r 295 s25, r 333 s25, r 334 s25, r 282 s16, r 296 s26, r 331 s16, r 378 s16, r 281
    s16, r 279 s16, r 269 s16, r 270 s16, r 376 s16, r 276 s16, r 267 s14, r 291 s16, r 329 s16, r 293 s16, r
    325 s30, r 372 s30, r 367 s30, r 320 s30, r 394 s56, r 266 s13, r 273 s19, r 292 s24, r 54 s6, r 38 s6, r
    190 s10, r 102 s6, r 86 s6, r 22 s6, r 14 s6, r 94 s6, r 182 s10, r 110 s6, r 222 s10, r 174 s10, r 198
    s10, r 214 s10, r 142 s10, r 78 s6, r 230 s10, r 166 s10, r 238 s10, r 46 s6, r 126 s6, r 150 s10, r 70
    s6, r 158 s10, r 246 s10, r 30 s6, r 62 s6, r 254 s10, r 262 s10, r 118 s6, r 134 s6, r 206 s10, r 280
    s15, r 375 s15, r 328 s15, r 268 s15, r 290 s15, r 275 s21, r 377 s44, r 330 s32, r 297 s27]

private theorem sortNode0 :
    Pdqsort.recurse 394 input0 (fun (left right : RegionShape) => left.key < right.key)
      none 9 true true = output0 := by
  kernel_rfl

private theorem sortNode1 :
    Pdqsort.recurse 393 input1 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 244 s9)) 8 false false = output1 := by
  kernel_rfl

private theorem stepSpec2
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input2 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 244 s9)) 9 false false =
      #[r 25 s4, r 6 s0, r 7 s0, r 364 s9, r 9 s4, r 362 s9, r 360 s9, r 12 s4, r 13 s4, r 359 s9, r 356 s9, r
    354 s9, r 17 s4, r 353 s9, r 350 s9, r 20 s4, r 21 s4, r 349 s0, r 241 s9, r 132 s4, r 137 s9, r 140 s9, r
    317 s4, r 28 s4, r 1 s0, r 315 s4, r 313 s4, r 312 s4, r 33 s4, r 309 s4, r 307 s4, r 36 s4, r 37 s4, r
    306 s4, r 303 s4, r 133 s4, r 41 s4, r 129 s4, r 141 s9, r 145 s9, r 298 s4, r 44 s4, r 45 s4, r 289 s4, r
    287 s4, r 286 s4, r 49 s4, r 283 s4, r 265 s12, r 52 s4, r 53 s4, r 264 s12, r 261 s9, r 260 s9, r 57 s4,
    r 257 s9, r 253 s9, r 60 s4, r 61 s4, r 252 s9, r 249 s9, r 245 s9, r 65 s4, r 29 s4, r 68 s4, r 5 s0, r
    69 s4, r 237 s9, r 236 s9, r 233 s9, r 73 s4, r 229 s9, r 228 s9, r 76 s4, r 77 s4, r 225 s9, r 221 s9, r
    220 s9, r 81 s4, r 217 s9, r 213 s9, r 84 s4, r 85 s4, r 212 s9, r 209 s9, r 205 s9, r 89 s4, r 204 s9, r
    201 s9, r 92 s4, r 93 s4, r 197 s9, r 196 s9, r 193 s9, r 97 s4, r 0 s0, r 189 s9, r 100 s4, r 101 s4, r
    188 s9, r 185 s9, r 181 s9, r 105 s4, r 180 s9, r 177 s9, r 108 s4, r 109 s4, r 173 s9, r 172 s9, r 169
    s9, r 113 s4, r 165 s9, r 164 s9, r 116 s4, r 117 s4, r 161 s9, r 157 s9, r 156 s9, r 121 s4, r 153 s9, r
    149 s9, r 124 s4, r 125 s4, r 148 s9] ++ rec input1 (some (r 244 s9)) 8 false false := by
  kernel_rfl

private theorem sortNode2 :
    Pdqsort.recurse 394 input2 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 244 s9)) 9 false false = output2 := by
  rw [Pdqsort.recurse, stepSpec2, sortNode1]
  kernel_rfl

private theorem stepSpec3
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input3 (fun (left right : RegionShape) => left.key < right.key)
      none 9 true true =
      rec input0 none 9 true true ++ #[r 244 s9] ++ rec input2 (some (r 244 s9)) 9 false false := by
  kernel_rfl

private theorem sortNode3 :
    Pdqsort.recurse 395 input3 (fun (left right : RegionShape) => left.key < right.key)
      none 9 true true = output3 := by
  rw [Pdqsort.recurse, stepSpec3, sortNode0, sortNode2]
  kernel_rfl

private theorem sortNode4 :
    Pdqsort.recurse 392 input4 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 54 s6)) 9 true true = output4 := by
  kernel_rfl

private theorem stepSpec5
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input5 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 54 s6)) 9 true true =
      #[r 38 s6, r 190 s10, r 102 s6, r 86 s6, r 22 s6, r 14 s6, r 94 s6, r 182 s10, r 110 s6, r 222 s10, r
    174 s10, r 198 s10, r 214 s10, r 142 s10, r 78 s6, r 230 s10, r 166 s10, r 238 s10, r 46 s6, r 126 s6, r
    150 s10, r 70 s6, r 158 s10, r 246 s10, r 30 s6, r 62 s6, r 254 s10, r 262 s10, r 118 s6, r 134 s6, r 206
    s10] ++ rec input4 (some (r 54 s6)) 9 true true := by
  kernel_rfl

private theorem sortNode5 :
    Pdqsort.recurse 393 input5 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 54 s6)) 9 true true = output5 := by
  rw [Pdqsort.recurse, stepSpec5, sortNode4]
  kernel_rfl

private theorem sortNode6 :
    Pdqsort.recurse 392 input6 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 55 s7)) 9 true true = output6 := by
  kernel_rfl

private theorem sortNode7 :
    Pdqsort.recurse 390 input7 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 299 s22)) 9 true true = output7 := by
  kernel_rfl

private theorem sortNode8 :
    Pdqsort.recurse 389 input8 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 282 s16)) 9 true false = output8 := by
  kernel_rfl

private theorem stepSpec9
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input9 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 282 s16)) 9 true false =
      #[r 296 s26, r 331 s16, r 378 s16, r 281 s16, r 279 s16, r 269 s16, r 270 s16, r 376 s16, r 276 s16, r
    267 s14, r 291 s16, r 329 s16, r 293 s16] ++ rec input8 (some (r 282 s16)) 9 true false := by
  kernel_rfl

private theorem sortNode9 :
    Pdqsort.recurse 390 input9 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 282 s16)) 9 true false = output9 := by
  rw [Pdqsort.recurse, stepSpec9, sortNode8]
  kernel_rfl

private theorem stepSpec10
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input10 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 299 s22)) 9 true false =
      rec input7 (some (r 299 s22)) 9 true true ++ #[r 282 s16] ++ rec input9 (some (r 282 s16)) 9 true false
    := by
  kernel_rfl

private theorem sortNode10 :
    Pdqsort.recurse 391 input10 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 299 s22)) 9 true false = output10 := by
  rw [Pdqsort.recurse, stepSpec10, sortNode7, sortNode9]
  kernel_rfl

private theorem stepSpec11
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input11 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 299 s22)) 9 true false =
      #[r 335 s22, r 294 s22, r 277 s22, r 368 s22, r 321 s22, r 379 s22, r 332 s22, r 373 s22, r 382 s22, r
    326 s22] ++ rec input10 (some (r 299 s22)) 9 true false := by
  kernel_rfl

private theorem sortNode11 :
    Pdqsort.recurse 392 input11 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 299 s22)) 9 true false = output11 := by
  rw [Pdqsort.recurse, stepSpec11, sortNode10]
  kernel_rfl

private theorem stepSpec12
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input12 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 55 s7)) 9 true false =
      rec input6 (some (r 55 s7)) 9 true true ++ #[r 299 s22] ++ rec input11 (some (r 299 s22)) 9 true false
    := by
  kernel_rfl

private theorem sortNode12 :
    Pdqsort.recurse 393 input12 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 55 s7)) 9 true false = output12 := by
  rw [Pdqsort.recurse, stepSpec12, sortNode6, sortNode11]
  kernel_rfl

private theorem stepSpec13
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input13 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 55 s7)) 9 true true =
      rec input12 (some (r 55 s7)) 9 true false ++ #[r 54 s6] ++ rec input5 (some (r 54 s6)) 9 true true := by
  kernel_rfl

private theorem sortNode13 :
    Pdqsort.recurse 394 input13 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 55 s7)) 9 true true = output13 := by
  rw [Pdqsort.recurse, stepSpec13, sortNode5, sortNode12]
  kernel_rfl

private theorem sortNode14 :
    Pdqsort.recurse 392 input14 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 344 s41)) 9 true true = output14 := by
  kernel_rfl

private theorem sortNode15 :
    Pdqsort.recurse 391 input15 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true true = output15 := by
  kernel_rfl

private theorem sortNode16 :
    Pdqsort.recurse 390 input16 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 248 s8)) 8 false false = output16 := by
  kernel_rfl

private theorem stepSpec17
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input17 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 248 s8)) 9 false false =
      #[r 16 s3, r 232 s8, r 224 s8, r 80 s3, r 216 s8, r 72 s3, r 8 s3, r 192 s8, r 240 s8, r 48 s3, r 88 s3,
    r 208 s8, r 24 s3, r 200 s8, r 96 s3, r 40 s3, r 144 s8, r 136 s8, r 64 s3, r 104 s3, r 32 s3, r 184 s8, r
    176 s8, r 256 s8, r 112 s3, r 168 s8, r 128 s3, r 160 s8, r 56 s3, r 152 s8, r 120 s3] ++ rec input16
    (some (r 248 s8)) 8 false false := by
  kernel_rfl

private theorem sortNode17 :
    Pdqsort.recurse 391 input17 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 248 s8)) 9 false false = output17 := by
  rw [Pdqsort.recurse, stepSpec17, sortNode16]
  kernel_rfl

private theorem stepSpec18
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input18 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false =
      rec input15 (some (r 98 s5)) 9 true true ++ #[r 248 s8] ++ rec input17 (some (r 248 s8)) 9 false false
    := by
  kernel_rfl

private theorem sortNode18 :
    Pdqsort.recurse 392 input18 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false = output18 := by
  rw [Pdqsort.recurse, stepSpec18, sortNode15, sortNode17]
  kernel_rfl

private theorem stepSpec19
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input19 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false =
      rec input18 (some (r 98 s5)) 9 true false ++ #[r 344 s41] ++ rec input14 (some (r 344 s41)) 9 true true
    := by
  kernel_rfl

private theorem sortNode19 :
    Pdqsort.recurse 393 input19 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false = output19 := by
  rw [Pdqsort.recurse, stepSpec19, sortNode14, sortNode18]
  kernel_rfl

private theorem stepSpec20
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input20 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false =
      #[r 26 s5, r 42 s5, r 43 s5, r 288 s5, r 138 s5, r 139 s5, r 131 s5, r 130 s5, r 50 s5, r 285 s5, r 284
    s5, r 51 s5, r 146 s5, r 147 s5, r 274 s20, r 271 s17, r 387 s49, r 305 s5, r 308 s5, r 123 s5, r 154 s5,
    r 155 s5, r 122 s5, r 35 s5, r 385 s47, r 310 s5, r 58 s5, r 259 s5, r 162 s5, r 163 s5, r 371 s5, r 115
    s5, r 370 s5, r 366 s5, r 258 s5, r 114 s5, r 170 s5, r 171 s5, r 59 s5, r 365 s5, r 10 s5, r 363 s5, r
    311 s5, r 11 s5, r 178 s5, r 179 s5, r 107 s5, r 106 s5, r 361 s5, r 358 s5, r 34 s5, r 314 s5, r 186 s5,
    r 187 s5, r 357 s5, r 251 s5, r 355 s5, r 18 s5, r 250 s5, r 99 s5, r 194 s5, r 195 s5, r 316 s5, r 19 s5,
    r 352 s5, r 351 s5, r 318 s5, r 66 s5, r 202 s5, r 203 s5, r 91 s5, r 90 s5, r 304 s5, r 27 s5, r 67 s5, r
    243 s5, r 210 s5, r 211 s5, r 242 s5, r 319 s5, r 323 s5, r 324 s5, r 235 s5, r 83 s5, r 218 s5, r 219 s5,
    r 82 s5, r 234 s5, r 74 s5, r 340 s37, r 75 s5, r 338 s35, r 226 s5, r 227 s5] ++ rec input19 (some (r 98
    s5)) 9 true false := by
  kernel_rfl

private theorem sortNode20 :
    Pdqsort.recurse 394 input20 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false = output20 := by
  rw [Pdqsort.recurse, stepSpec20, sortNode19]
  kernel_rfl

private theorem stepSpec21
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input21 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false =
      rec input20 (some (r 98 s5)) 9 true false ++ #[r 55 s7] ++ rec input13 (some (r 55 s7)) 9 true true := by
  kernel_rfl

private theorem sortNode21 :
    Pdqsort.recurse 395 input21 (fun (left right : RegionShape) => left.key < right.key)
      (some (r 98 s5)) 9 true false = output21 := by
  rw [Pdqsort.recurse, stepSpec21, sortNode13, sortNode20]
  kernel_rfl

private theorem stepSpec22
    (rec : Array RegionShape → Option RegionShape → Nat → Bool → Bool → Array RegionShape) :
    Pdqsort.recurseStep rec input22 (fun (left right : RegionShape) => left.key < right.key)
      none 9 true true =
      rec input3 none 9 true true ++ #[r 98 s5] ++ rec input21 (some (r 98 s5)) 9 true false := by
  kernel_rfl

private theorem sortNode22 :
    Pdqsort.recurse 396 input22 (fun (left right : RegionShape) => left.key < right.key)
      none 9 true true = output22 := by
  rw [Pdqsort.recurse, stepSpec22, sortNode3, sortNode21]
  kernel_rfl


private theorem input_eq_source :
    (indexRegionSummaries 0 actionOrderedRegionShapes).toArray = input22 := by
  kernel_rfl

private theorem quicksort_eq_recurse (values : Array RegionShape) (hsize : values.size = 395) :
    Pdqsort.quicksort values (fun left right => left.key < right.key) =
      Pdqsort.recurse 396 values (fun left right => left.key < right.key) none 9 true true := by
  simp only [Pdqsort.quicksort, hsize]
  rfl

/-- Every indexed region in the exact descending order used by V1. -/
def actionSortedRegionShapes : List RegionShape := output22.reverse.toList

/-- Region identifiers in that order, kept as a small explicit placement input. -/
def actionSortedRegionIndices : List ℕ :=
  [297, 330, 377, 275, 290, 268, 328, 375, 280, 206, 134, 118, 262, 254, 62, 30, 246, 158, 70, 150, 126, 46,
    238, 166, 230, 78, 142, 214, 198, 174, 222, 110, 182, 94, 14, 22, 86, 102, 190, 38, 54, 292, 273, 266,
    394, 320, 367, 372, 325, 293, 329, 291, 267, 276, 376, 270, 269, 279, 281, 378, 331, 296, 282, 334, 333,
    295, 381, 380, 326, 382, 373, 332, 379, 321, 368, 277, 294, 335, 299, 31, 247, 322, 255, 374, 135, 239,
    327, 119, 39, 263, 159, 167, 231, 369, 79, 223, 151, 127, 215, 87, 207, 23, 199, 95, 143, 47, 71, 191,
    103, 15, 183, 175, 111, 63, 55, 300, 272, 278, 342, 393, 345, 392, 341, 391, 389, 388, 344, 336, 383,
    337, 384, 120, 152, 56, 160, 128, 168, 112, 256, 176, 184, 32, 104, 64, 136, 144, 40, 96, 200, 24, 208,
    88, 48, 240, 192, 8, 72, 216, 80, 224, 232, 16, 248, 343, 390, 386, 339, 227, 226, 338, 75, 340, 74,
    234, 82, 219, 218, 83, 235, 324, 323, 319, 242, 211, 210, 243, 67, 27, 304, 90, 91, 203, 202, 66, 318,
    351, 352, 19, 316, 195, 194, 99, 250, 18, 355, 251, 357, 187, 186, 314, 34, 358, 361, 106, 107, 179,
    178, 11, 311, 363, 10, 365, 59, 171, 170, 114, 258, 366, 370, 115, 371, 163, 162, 259, 58, 310, 385, 35,
    122, 155, 154, 123, 308, 305, 387, 271, 274, 147, 146, 51, 284, 285, 50, 130, 131, 139, 138, 288, 43,
    42, 26, 98, 2, 3, 4, 348, 347, 301, 148, 125, 124, 149, 153, 121, 156, 157, 161, 117, 116, 164, 165,
    113, 169, 172, 173, 109, 108, 177, 180, 105, 181, 185, 188, 101, 100, 189, 0, 97, 193, 196, 197, 93, 92,
    201, 204, 89, 205, 209, 212, 85, 84, 213, 217, 81, 220, 221, 225, 77, 76, 228, 229, 73, 233, 236, 237,
    69, 5, 68, 29, 65, 245, 249, 252, 61, 60, 253, 257, 57, 260, 261, 264, 53, 52, 265, 283, 49, 286, 287,
    289, 45, 44, 298, 145, 141, 129, 41, 133, 303, 306, 37, 36, 307, 309, 33, 312, 313, 315, 1, 28, 317,
    140, 137, 132, 241, 349, 21, 20, 350, 353, 17, 354, 356, 359, 13, 12, 360, 362, 9, 364, 7, 6, 25, 244,
    346, 302]

/-- The legacy sorter, including ties, computes the certified descending sequence. -/
theorem actionOrderedRegionShapes_sorted :
    (Pdqsort.quicksort (indexRegionSummaries 0 actionOrderedRegionShapes).toArray
      (fun left right => left.key < right.key)).reverse.toList = actionSortedRegionShapes := by
  have hquick := (quicksort_eq_recurse input22 rfl).trans sortNode22
  exact (congrArg (fun values : Array RegionShape =>
    (Pdqsort.quicksort values (fun left right => left.key < right.key)).reverse.toList)
      input_eq_source).trans
        (congrArg (fun values : Array RegionShape => values.reverse.toList) hquick)

/-- The explicit index list is the projection of the complete sorted records. -/
theorem actionSortedRegionShapes_indices :
    actionSortedRegionShapes.map RegionShape.index = actionSortedRegionIndices := by
  kernel_rfl

/-- Both empty regions are retained in the sorted sequence. -/
theorem actionSortedRegionShapes_length : actionSortedRegionShapes.length = 395 := by
  kernel_rfl

end

end Zcash.Snark.ZeroKnowledge
