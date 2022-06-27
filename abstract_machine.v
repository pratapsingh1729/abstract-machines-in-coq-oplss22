Require Import List.
Import ListNotations.

Definition var := nat.
Definition eqb_var := Nat.eqb. 
Definition covar := nat.
Definition eqb_covar := Nat.eqb. 

Inductive term : Set :=
| tVar : var -> term
| tT : term
| tF : term
| tLam : var -> term -> term
| tMu : covar -> com -> term
with kont : Set :=
| kCovar : covar -> kont
| kStack : term -> kont -> kont
| kCond : com -> com -> kont
with com : Set :=
| cCom : term -> kont -> com.

Inductive ty : Set :=
| Tbool : ty
| Tarr : ty -> ty -> ty.

Definition ctxt : Type := list (var * ty).
Definition coctxt : Type := list (covar * ty).

Inductive term_typed : ctxt -> term -> ty -> coctxt -> Prop :=
| arrowR : forall Γ x v A B Δ,
    term_typed ((x,A) :: Γ) v B Δ ->
    term_typed Γ (tLam x v) (Tarr A B) Δ
| boolR1 : forall Γ Δ,
    term_typed Γ tT Tbool Δ
| boolR2 : forall Γ Δ,
    term_typed Γ tF Tbool Δ
| Ax : forall Γ x A Δ,
    term_typed ((x,A) :: Γ) (tVar x) A Δ
| ActR : forall c Γ α A Δ,
    com_typed c Γ ((α, A) :: Δ) ->
    term_typed Γ (tMu α c) A Δ
with kont_typed : ctxt -> kont -> ty -> coctxt -> Prop :=
| arrowL : forall Γ v E A B Δ,
    term_typed Γ v A Δ ->
    kont_typed Γ E B Δ ->
    kont_typed Γ (kStack v E) (Tarr A B) Δ
| boolL : forall Γ c1 c2 Δ,
    com_typed c1 Γ Δ ->
    com_typed c2 Γ Δ ->
    kont_typed Γ (kCond c1 c2) Tbool Δ
| CoAx : forall Γ α A Δ,
    kont_typed Γ (kCovar α) A ((α, A) :: Δ)
with com_typed : com -> ctxt -> coctxt -> Prop :=
| Cut : forall Γ v A Δ E,
    term_typed Γ v A Δ ->
    kont_typed Γ E A Δ ->
    com_typed (cCom v E) Γ Δ.

Notation "<[ G ⊢ V ; T | D ]>" := (term_typed G V T D) (at level 50).
Notation "<| G | E ; T ⊢ D |>" := (kont_typed G E T D) (at level 50).
Notation "<{ C ; ( G , D ) }>" := (com_typed C G D) (at level 50).

Lemma true_admits_bool: forall Γ Δ,
  <[ Γ ⊢ tT ; Tbool | Δ ]>.
Proof. constructor. Qed.

Lemma CoAx_holds : forall Γ α A Δ,
  <| Γ | (kCovar α) ; A ⊢ (α, A) :: Δ |>.
Proof. constructor. Qed.

Fail Fixpoint subst_var_term (x : var) (M : term) (N : term) : term :=
  match N with
  | tVar y => if eqb_var x y then M else N
  | tT => tT
  | tF => tF
  | tLam y N' => if eqb_var x y then N else (tLam y (subst_var_term x M N'))
  | tMu α c => tMu α (subst_var_com x M c)
  end
with subst_var_kont (x : var) (M : term) (E : kont) : kont :=
  match E with
  | kCovar α => E
  | kStack N E' => kStack (subst_var_term x M N) (subst_var_kont x M E)
  | kCond c1 c2 => kCond (subst_var_com x M c1) (subst_var_com x M c2)
  end
with subst_var_com (x : var) (M : term) (c : com) : com :=
  match c with
  | cCom N E => cCom (subst_var_term x M N) (subst_var_kont x M E)
  end.
(* Coq cannot guess the decreasing argument *)    



