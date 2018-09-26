From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_prop mf_tight mf_prod.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section sums.
Context (S T S' T': Type).
(* A modification of the following construction is used to define the sum of represented spaces. *)
Definition mfss S T S' T' (f : S ->> T) (g : S' ->> T') :=
  make_mf (fun c x => match c with
    | inl a => match x with
      | inl y => f a y
      | inr z => False
    end
    | inr b => match x with
      | inl y => False
      | inr z => g b z
    end
  end).
Notation "f +s+ g" := (mfss f g) (at level 50).

Definition mfss_fun S T S' T' (f: S -> T) (g: S' -> T') :=
	fun ss' => match ss' with
		| inl s => inl (f s)
		| inr s' => inr (g s')
	end.
Notation "f +s+_f g" := (mfss_fun f g) (at level 50).

Lemma mfss_fun_mfss (f: S -> T) (g: S' -> T'):
	F2MF (mfss_fun f g) =~= mfss (F2MF f) (F2MF g).
Proof.
split; rewrite /F2MF; first by move <-; case s => /=.
by case: s => /=; case: s0 => //= s t ->.
Qed.
End sums.
Notation "f '+s+' g" := (mfss f g) (at level 50).
Notation "f '+s+_f' g" := (mfss_fun f g) (at level 50).