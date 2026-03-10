--! # LeanStlc : de Bruijn indexed stlc with logical relations for normalization and type safety -!/


import LeanStlc.Syntax
import LeanStlc.Typing
import LeanStlc.Reachable
import LeanStlc.Evaluation
import LeanStlc.Normalization

/-!
  ## Code structure
  all code is in the `LeanStlc` namespace, and is organized into the following files:
  - `Syntax.lean` : defines the syntax of the language, including renaming, substitution and related lemmas
  - `Reachable.lean` : defines the notion of reachability for evaluation steps
  - `Evaluation.lean` : defines the evaluation rules and evaluation judgments
  - `Typing.lean` : defines the typing rules and typing judgments
  - `Normalization.lean` : defines the logical relations and proves normalization and type safety

  the dependencies between the files are as follows:
  ```mermaid
  graph LR
    Syntax --> Evaluation
    Reachable --> Evaluation
    Syntax --> Typing
    Syntax --> Normalization
    Evaluation --> Normalization
    Typing --> Normalization
  ```

  ## Guidelines for reading the codex
  There are two hard points for newbies to understand the mechanization of logical relations:
  1. the definition of the logical relatio
    there are mutually recursive definitions over values and expressions
    and involves a lot of quantification over contexts and substitutions
	$⟦ A ⟧ ∋ v$ defines that $v$ is a value with type $A$, especially that
	$⟦ A → B ⟧ ∋ λ. e$ requires that forall $a ∈ ⟦ A ⟧$, $e⦃⟨a⟩⦄ ⟶* v' ∈ ⟦ B ⟧$
	to strengthen the premise when proving the `app` case.
	$e⦃⟨a⟩⦄ ⟶* v' ∈ ⟦ B ⟧$ is a bit complex, we should introduce the notion of $ℰ⟦ B ⟧$,
	denoting it as $e⦃⟨a⟩⦄ ∈ ℰ⟦ B ⟧$.
	And for the semantic typing judgement (`LeanStlc.Normalization.semTyp`) $Γ ⊨ e : A$,
	we require that for all substitutions $σ$ for the context $Γ$ (`LeanStlc.Normalization.wfSubst`),
	i.e. forall $σ ∈ ⟦ Γ ⟧$, $e⦃σ⦄ ∈ ℰ⟦ A ⟧$.


  2. the de Bruijn index representation of variables
    Due to the substitution nature of $Γ ⊨ e : A$,
	it will introduce a double substitution when meeting a variable-binding case,
    e.g. the `lam` case in the proof of normalization,
	where we need to prove $Γ ⊨ λ. e : A → B$,
    which requires us to prove $Γ, A ⊨ e : B$,
    and by the definition of the logical relation,
    $Γ ⊢ e : B$ introduces a substitution $σ$ for the context $Γ$,
    and the ⟦ A → B ⟧ in the `lam` case introduces another singleton substitution $⟨a⟩$,
    finally making us to prove $e⦃σ⦄⦃⟨a⟩⦄ ∈ ⟦ B ⟧$,
    the double substitution $e⦃σ⦄⦃⟨a⟩⦄$ requiring a lemma `LeanStlc.Syntax.substCons`.

  We will explain these two hard points in the comments of the corresponding code,
  and also provide some intuition and motivation for the definitions and proofs.

 -/
