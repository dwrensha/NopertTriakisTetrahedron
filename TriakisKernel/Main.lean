/-
The final module of the kernel-only proof that the 11/20 triakis tetrahedron is not Rupert.

This is the only checked-in file under `TriakisKernel/`; every module it imports is generated
from the certificate packs and is not in the repository. To produce and check them, run from the
repository root:

    scripts/fetch_packs.sh      # the certificate packs, into packs/
    scripts/gen_kernel.sh       # the generated modules, into TriakisKernel/
    lake build TriakisKernel  # checks everything (several hours; see README.md)

Every certificate here is checked by `decide +kernel`, so the proof does not depend on
`Lean.ofReduceBool` or compiled code; the `#print axioms` at the end confirms this.
-/
import TriakisKernel.Chart.Assembly
import TriakisKernel.Local.Assembly
import Noperts.Triakis.IsNotRupert
import TriakisKernel.T0.Table
import TriakisKernel.T1.Table
import TriakisKernel.T2.Table
import TriakisKernel.T3.Table
import TriakisKernel.T4.Table
import TriakisKernel.T5.Table
import TriakisKernel.T6.Table
import TriakisKernel.T7.Table
import TriakisKernel.T8.Table
import TriakisKernel.T9.Table
import TriakisKernel.T10.Table
import TriakisKernel.T11.Table
import TriakisKernel.T12.Table
import TriakisKernel.T13.Table
import TriakisKernel.T14.Table
import TriakisKernel.T15.Table
import TriakisKernel.T16.Table
import TriakisKernel.T17.Table
import TriakisKernel.T18.Table
import TriakisKernel.T19.Table
import TriakisKernel.T20.Table
import TriakisKernel.T21.Table
import TriakisKernel.T22.Table
import TriakisKernel.T23.Table
import TriakisKernel.T24.Table
import TriakisKernel.T25.Table
import TriakisKernel.T26.Table
import TriakisKernel.T27.Table
import TriakisKernel.T28.Table
import TriakisKernel.T29.Table
import TriakisKernel.T30.Table
import TriakisKernel.T31.Table
import TriakisKernel.T32.Table
import TriakisKernel.T33.Table
import TriakisKernel.T34.Table
import TriakisKernel.T35.Table
import TriakisKernel.T36.Table
import TriakisKernel.T37.Table
import TriakisKernel.T38.Table
import TriakisKernel.T39.Table
import TriakisKernel.T40.Table
import TriakisKernel.T41.Table
import TriakisKernel.T42.Table
import TriakisKernel.T43.Table
import TriakisKernel.T44.Table
import TriakisKernel.T45.Table
import TriakisKernel.T46.Table
import TriakisKernel.T47.Table
import TriakisKernel.T48.Table
import TriakisKernel.T49.Table
import TriakisKernel.T50.Table
import TriakisKernel.T51.Table
import TriakisKernel.T52.Table
import TriakisKernel.T53.Table
import TriakisKernel.T54.Table
import TriakisKernel.T55.Table
import TriakisKernel.T56.Table
import TriakisKernel.T57.Table
import TriakisKernel.T58.Table
import TriakisKernel.T59.Table
import TriakisKernel.T60.Table
import TriakisKernel.T61.Table
import TriakisKernel.T62.Table
import TriakisKernel.T63.Table
import TriakisKernel.T64.Table
import TriakisKernel.T65.Table
import TriakisKernel.T66.Table
import TriakisKernel.T67.Table
import TriakisKernel.T68.Table
import TriakisKernel.T69.Table
import TriakisKernel.T70.Table
import TriakisKernel.T71.Table
import TriakisKernel.T72.Table
import TriakisKernel.T73.Table
import TriakisKernel.T74.Table
import TriakisKernel.T75.Table
import TriakisKernel.T76.Table
import TriakisKernel.T77.Table
import TriakisKernel.T78.Table
import TriakisKernel.T79.Table
import TriakisKernel.T80.Table
import TriakisKernel.T81.Table
import TriakisKernel.T82.Table
import TriakisKernel.T83.Table
import TriakisKernel.T84.Table
import TriakisKernel.T85.Table

open Noperts.Triakis Noperts.Triakis.CornerTree Noperts.Triakis.CornerCoverage
open Noperts.Triakis.AtlasProjectiveSolutionTree

set_option Elab.async false

namespace Noperts.Triakis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every corner case is covered: each field is discharged by its corner table. -/
theorem kernel_cov : Cov cornerEps where
  tpocket face m hH := by
    fin_cases face <;> fin_cases m
    · exact KernelCorner.T77.table_covered hH
    · exact KernelCorner.T78.table_covered hH
    · exact KernelCorner.T79.table_covered hH
    · exact KernelCorner.T80.table_covered hH
    · exact KernelCorner.T81.table_covered hH
    · exact KernelCorner.T82.table_covered hH
  ppocket k m hH := by
    fin_cases k <;> fin_cases m
    · exact KernelCorner.T71.table_covered hH
    · exact KernelCorner.T72.table_covered hH
    · exact KernelCorner.T73.table_covered hH
    · exact KernelCorner.T74.table_covered hH
    · exact KernelCorner.T75.table_covered hH
    · exact KernelCorner.T76.table_covered hH
    · exact KernelCorner.T83.table_covered hH
    · exact KernelCorner.T84.table_covered hH
    · exact KernelCorner.T85.table_covered hH
  spocket m hH := by
    fin_cases m
    · exact KernelCorner.T68.table_covered hH
    · exact KernelCorner.T69.table_covered hH
    · exact KernelCorner.T70.table_covered hH
  pocket k m hH := by
    fin_cases k <;> fin_cases m
    · exact KernelCorner.T59.table_covered hH
    · exact KernelCorner.T60.table_covered hH
    · exact KernelCorner.T61.table_covered hH
    · exact KernelCorner.T62.table_covered hH
    · exact KernelCorner.T63.table_covered hH
    · exact KernelCorner.T64.table_covered hH
    · exact KernelCorner.T65.table_covered hH
    · exact KernelCorner.T66.table_covered hH
    · exact KernelCorner.T67.table_covered hH
  cone neg hH := by
    have e : neg = ![neg 0, neg 1, neg 2, neg 3] := by funext i; fin_cases i <;> rfl
    rw [e]
    generalize neg 0 = a; generalize neg 1 = b; generalize neg 2 = c; generalize neg 3 = d
    cases a <;> cases b <;> cases c <;> cases d
    · exact KernelCorner.T43.table_covered hH
    · exact KernelCorner.T51.table_covered hH
    · exact KernelCorner.T47.table_covered hH
    · exact KernelCorner.T55.table_covered hH
    · exact KernelCorner.T45.table_covered hH
    · exact KernelCorner.T53.table_covered hH
    · exact KernelCorner.T49.table_covered hH
    · exact KernelCorner.T57.table_covered hH
    · exact KernelCorner.T44.table_covered hH
    · exact KernelCorner.T52.table_covered hH
    · exact KernelCorner.T48.table_covered hH
    · exact KernelCorner.T56.table_covered hH
    · exact KernelCorner.T46.table_covered hH
    · exact KernelCorner.T54.table_covered hH
    · exact KernelCorner.T50.table_covered hH
    · exact KernelCorner.T58.table_covered hH
  tube seg face hH := by
    cases seg <;> fin_cases face
    · exact KernelCorner.T7.table_covered hH
    · exact KernelCorner.T8.table_covered hH
    · exact KernelCorner.T9.table_covered hH
    · exact KernelCorner.T10.table_covered hH
    · exact KernelCorner.T11.table_covered hH
    · exact KernelCorner.T12.table_covered hH
    · exact KernelCorner.T25.table_covered hH
    · exact KernelCorner.T26.table_covered hH
    · exact KernelCorner.T27.table_covered hH
    · exact KernelCorner.T28.table_covered hH
    · exact KernelCorner.T29.table_covered hH
    · exact KernelCorner.T30.table_covered hH
  wtube seg face hH := by
    cases seg <;> fin_cases face
    · exact KernelCorner.T14.table_covered hH
    · exact KernelCorner.T15.table_covered hH
    · exact KernelCorner.T16.table_covered hH
    · exact KernelCorner.T17.table_covered hH
    · exact KernelCorner.T32.table_covered hH
    · exact KernelCorner.T33.table_covered hH
    · exact KernelCorner.T34.table_covered hH
    · exact KernelCorner.T35.table_covered hH
  wedge seg hH := by
    cases seg
    · exact KernelCorner.T13.table_covered hH
    · exact KernelCorner.T31.table_covered hH
  skew hH := KernelCorner.T36.table_covered hH
  zero face hH := by
    fin_cases face
    · exact KernelCorner.T37.table_covered hH
    · exact KernelCorner.T38.table_covered hH
    · exact KernelCorner.T39.table_covered hH
    · exact KernelCorner.T40.table_covered hH
    · exact KernelCorner.T41.table_covered hH
    · exact KernelCorner.T42.table_covered hH
  plain seg face hH := by
    cases seg <;> fin_cases face
    · exact KernelCorner.T0.table_covered hH
    · exact KernelCorner.T1.table_covered hH
    · exact KernelCorner.T2.table_covered hH
    · exact KernelCorner.T3.table_covered hH
    · exact KernelCorner.T4.table_covered hH
    · exact KernelCorner.T5.table_covered hH
    · exact KernelCorner.T6.table_covered hH
    · exact KernelCorner.T18.table_covered hH
    · exact KernelCorner.T19.table_covered hH
    · exact KernelCorner.T20.table_covered hH
    · exact KernelCorner.T21.table_covered hH
    · exact KernelCorner.T22.table_covered hH
    · exact KernelCorner.T23.table_covered hH
    · exact KernelCorner.T24.table_covered hH

theorem kernel_cornerCovered : CornerCovered := kernel_cov.covered

/-- The 11/20 triakis tetrahedron is not Rupert: every step checked by the kernel. -/
theorem triakis_not_rupert_kernel : ¬ IsRupert exactVerts :=
  not_rupert_of_root (ChartK.chart_root LocalK.headers_covered kernel_cornerCovered)

end Noperts.Triakis

#print axioms Noperts.Triakis.triakis_not_rupert_kernel
