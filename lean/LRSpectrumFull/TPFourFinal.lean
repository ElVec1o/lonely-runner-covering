/-
# TP'(4): the theorem

`TPp 4`: for four distinct positive integer speeds and any integer phases `s_i / 5`, some real time has every
runner at distance at least `1/5` from an integer.  Chain: `case3` (TPFourCase3) gives `Case3`;
`caseH_of_case3` (TPFourGlue) gives `CaseH`; `TPp_four_of_caseH` (TPFourReduce) gives `TPp 4`.
-/
import LRSpectrumFull.TPFourCase3

namespace LRSpectrumFull

theorem TPp_four : TPp 4 := TPp_four_of_caseH (caseH_of_case3 case3)

end LRSpectrumFull
