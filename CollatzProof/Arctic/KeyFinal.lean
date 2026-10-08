/-
Conclusion of the swap argument: proof of the hypothesis `HKeyTop` (`HTWKey.lean`, uniformity of the top bits of a single chunk; Theorem B.7)
and of `HTerrasWin` (Theorem B.8).
* Assembly (Theorem B.7): `KeyMain4.hKeyTop_of_specs` (the Terras algebra and the swap translations are in `KeyTerras*`).
* Analytic ingredients: `KeyAnal.specCells` ((Q3)), `KeyAnal3.specQavg` (Proposition B.6), `KeyAnal4.specNine`
  (order of 9), `KeyAnal5.specDoeblin` (Doeblin bound).
-/
import CollatzProof.Arctic.KeyMain4
import CollatzProof.Arctic.KeyAnal3
import CollatzProof.Arctic.KeyAnal4
import CollatzProof.Arctic.KeyAnal5
import CollatzProof.Arctic.HTWFromKey

namespace Collatz.Arctic

/-- **`HKeyTop` holds** (Theorem B.7). -/
theorem hKeyTop : HKeyTop := hKeyTop_of_specs specCells specQavg specNine specDoeblin

/-- **`HTerrasWin` holds** (Theorem B.8, window frequencies). -/
theorem hTerrasWin : HTerrasWin := hTerrasWin_of_key hKeyTop

end Collatz.Arctic
