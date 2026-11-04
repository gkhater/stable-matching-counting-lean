import StableMatching.UniformQueryParameters
import StableMatching.RawSATInput

/-! Applied closure lemmas keep the uniform compiler certificates modular. -/

namespace StableMatching.QueryPolyApplications

open Groundwork

variable {A : Type} [Enc A]

theorem varsFuel {code : A → List Bool} {blocks : A → RawChainCut.Blocks}
    (hc : PolyT code) (hb : PolyT blocks) :
    PolyT (fun a => UniformQueryParameters.varsFuel (code a) (blocks a)) :=
  Groundwork.PolyT.comp
    (f := fun p : List Bool × RawChainCut.Blocks => UniformQueryParameters.varsFuel p.1 p.2)
    (g := fun a : A => (code a, blocks a))
    UniformQueryParameters.varsFuel_polyT (Groundwork.PolyT.prodMk hc hb)

theorem prepare {fuel : A → List Unit} {raw : A → RawChainCut.RawCNF}
    (hf : PolyT fuel) (hr : PolyT raw) :
    PolyT (fun a => RawSATInput.prepare (fuel a) (raw a)) :=
  Groundwork.PolyT.comp
    (f := fun p : List Unit × RawChainCut.RawCNF => RawSATInput.prepare p.1 p.2)
    (g := fun a : A => (fuel a, raw a)) RawSATInput.prepare_polyT (Groundwork.PolyT.prodMk hf hr)

theorem encodeInput {width vars : A → List Unit} {raw : A → RawChainCut.RawCNF}
    (hw : PolyT width) (hv : PolyT vars) (hr : PolyT raw) :
    PolyT (fun a => RawSATInput.encodeInput (width a) (vars a) (raw a)) :=
  RawSATInput.encodeInput_polyT.comp (PolyT.prodMk (PolyT.prodMk hw hv) hr)

end StableMatching.QueryPolyApplications
