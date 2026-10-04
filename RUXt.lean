/-
RUXt: the root module, importing the whole development.
-/
import RUXt.Lib.PFun
import RUXt.Lib.Telescopes
import RUXt.Lang.Types.Basic
import RUXt.Lang.Types.Params
import RUXt.Lang.Expr
import RUXt.Lang.Functions.Basic
import RUXt.Lang.Functions.Library
import RUXt.Lang.Typechecker
import RUXt.Lang.Semantics
import RUXt.Model.Logic
import RUXt.Model.Summary.Basic
import RUXt.Model.Summary.Derive
import RUXt.Model.Summary.Specialise
import RUXt.Model.Refute
import RUXt.Semantics.Logic.Asrt
import RUXt.Semantics.Logic.Basic
import RUXt.Semantics.Logic.Poly
import RUXt.Semantics.Logic.Solver
import RUXt.Semantics.Summary.Subvariant.Basic
import RUXt.Semantics.Summary.Subvariant.Specialise
import RUXt.Semantics.Summary.Source.Basic
import RUXt.Semantics.Summary.Source.Specialise
import RUXt.Semantics.Summary.Basic
import RUXt.Semantics.Summary.Derive
import RUXt.Semantics.Summary.Specialise
import RUXt.Semantics.Witness
import RUXt.Semantics.Inadequacy
import RUXt.Examples.RISL
import RUXt.Examples.Calls
import RUXt.Examples.Even
import RUXt.Examples.Box.Library
import RUXt.Examples.Box
-- import RUXt.Types.Ty
-- import RUXt.Types.Lib.Int
-- import RUXt.Types.Lib.Bool
-- import RUXt.Types.Lib.Unit
-- import RUXt.Types.Lib.Own
-- import RUXt.Types.Rules
-- import RUXt.Types.Validity
