From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_rcmp mf_comp mf_tot mf_sing mf_tight mf_prod.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section functions.
Context (S T S' T': Type).

Definition cnst S T (c: T) := (fun (_: S) => c).

Definition mf_cnst S T (c: T) := F2MF (@cnst S T c).
Arguments mf_cnst {S} {T}.

Lemma cnst_rcmp R (c: T) (f: R ->> S): (mf_cnst c) o_R f =~= (mf_cnst c)|_(dom f).
Proof. by move => r t; split => [[s [fst <-]] | [[s] frs <-]]; first split; try by exists s. Qed.

Lemma cnst_comp R (c: T) (f: R ->> S): (mf_cnst c) o f =~= (mf_cnst c)|_(dom f).
Proof.
move => r t.
split; first by rewrite /=/cnst; move => [[s [frs /=->]] _]; split => //; exists s.
move => [[s fsr <-]]; split; first by exists s.
by move => a b; exists c.
Qed.

Lemma fprd_id: @mf_id S ** @mf_id S' =~= @mf_id (S * S').
Proof. by move => [s s'] [t t'] /=;split; by move => [-> ->]. Qed.

Definition mf_fst S T := (F2MF (@fst S T)).
Arguments mf_fst {S} {T}.

Lemma fprd_fst (f: S ->> T) (g: S' ->> T') : mf_fst o (f ** g) =~= f o mf_fst|_(All \x dom g).
Proof.
move => s t; rewrite comp_F2MF.
split => [[[[t' t''] [[/= fs1t' gs2t'']]] /=<- _] | [[_ [t' gs2t']] fst]].
	split => //; split => //; by exists t''.
rewrite comp_rcmp; last exact /F2MF_tot.
by exists (t, t').
Qed.

Definition mf_snd S T := (F2MF (@snd S T)).
Arguments mf_snd {S} {T}.

Lemma fprd_snd (f: S ->> T) (g: S' ->> T') : mf_snd o (f ** g) =~= g o mf_snd|_(dom f \x All).
Proof.
move => s t; rewrite comp_F2MF.
split => [[[[t' t''] [[/= fs1t' gs2t'']]] /=<- _] | [[[t' gs2t'] _] fst]].
	split => //; split => //; by exists t'.
rewrite comp_rcmp; last exact /F2MF_tot.
by exists (t', t).
Qed.

Definition diag S := fun (d: S) => (d,d).
Arguments diag {S}.
Definition mf_diag S := F2MF (@diag S).
Arguments mf_diag {S}.

Lemma tight_fprd_diag (f: S ->> T): (mf_diag o f) \tightens ((f ** f) o mf_diag).
Proof.
apply split_tight => [ | s sfd [_ _] [[t] [fst [<- <-]] _]]; last by rewrite comp_F2MF.
rewrite comp_F2MF => s [[t t'] [fst fst']].
rewrite comp_rcmp; last exact /F2MF_tot.
exists (t, t); exists t; split => //.
Qed.

Lemma fprd_diag (f: S ->> T): f \is_singlevalued -> (f ** f) o mf_diag =~= mf_diag o f.
Proof.
rewrite comp_F2MF comp_rcmp; last exact /F2MF_tot.
move => sing s [t1 t2].
split => [[fst1 fst2] | ]; last by move => [t] [fst [<- <-]].
by exists t1; split => //; rewrite (sing s t2 t1).
Qed.

Lemma fprd_diag_sing (f: S ->> T): ((f ** f) o mf_diag) \tightens (mf_diag o f) -> f \is_singlevalued.
Proof.
move => tight.
have: ((f ** f) o mf_diag) =~= (mf_diag o f) by apply/tight_equiv/tight_fprd_diag.
rewrite comp_F2MF comp_rcmp; last exact /F2MF_tot.
by move => eq s t t'; intros; have /=[ | t'' [fst'' [<- <-]]]//:= (eq s (t, t')).1.
Qed.

Definition uncurry R S T (E: R * S -> T) r:= (fun s => E (r,s)).
Definition mf_uncurry R S T (E: R * S ->> T) r := make_mf (fun s t => E (r, s) t).

Lemma F2MF_ncry R (E: R * S -> T) r:
	F2MF (uncurry E r) =~= mf_uncurry (F2MF E) r.
Proof. done. Qed.

Lemma mf_ncry_prp R (E: R * S ->> T) r:
	mf_uncurry E r =~= E o ((mf_cnst r) ** mf_id) o mf_diag.
Proof. by rewrite -F2MF_fprd comp_assoc !comp_F2MF => s t/=. Qed.
End functions.
Arguments cnst {S} {T}.
Arguments mf_cnst {S} {T}.
Arguments diag {S}.
Arguments mf_diag {S}.
Arguments mf_fst {S} {T}.
Arguments mf_snd {S} {T}.