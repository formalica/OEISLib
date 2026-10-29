import Scripts.Templates.Coxeter
import Scripts.Templates.PrimeCongruent
import Scripts.Templates.SqrtContinuedFraction
import Scripts.Templates.WalkN3

/-!
Registry of the templates known to `lake exe oeis-template`. A new template is a module
`Scripts/Templates/<Name>.lean` defining a `Template` value, imported and listed here.
-/

namespace Oeis.Template

/-- All available templates. -/
def templates : Array Template :=
  #[WalkN3.template, PrimeCongruent.template, SqrtContinuedFraction.template, Coxeter.template]

/-- Looks a template up by (case-sensitive) name. -/
def findTemplate? (name : String) : Option Template :=
  templates.find? fun t => t.name == name

end Oeis.Template
