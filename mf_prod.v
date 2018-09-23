(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_prop mf_tight.
Require Import CRelationClasses Morphisms Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section products_sums.
Context (S T S' T': Type).
(* A modification of the following construction is used to define the product of represented spaces. *)

Definition mfpp S T S' T' (f : S ->> T) (g : S' ->> T') :=
	make_mf (fun c x => f c.1 x.1 /\ g c.2 x.2).
Notation "f '**' g" := (mfpp f g) (at level 50).

Global Instance mfpp_prpr S T S' T':
Proper ((@equiv S T) ==> (@equiv S' T') ==> (@equiv (S * S') (T * T'))) (@mfpp S T S' T').
Proof.
move => f f' eq g g' eq' r t.
by rewrite /mfpp /= eq eq'.
Qed.

Lemma mfpp_id: @mf_id S ** @mf_id S' =~= @mf_id (S * S').
Proof. by move => [s s'] [t t'] /=;split; by move => [-> ->]. Qed.

Definition mf_fst S T := (F2MF (@fst S T)).
Arguments mf_fst {S} {T}.

Lemma mfpp_fst (f: S ->> T) (g: S' ->> T') : mf_fst o (f ** g) =~= f o mf_fst|_(All \x dom g).
Proof.
move => s t.
rewrite F2MF_comp.
split => [[[[t' t''] [[/= fs1t' gs2t'']]] /=<- _] | [[_ [t' gs2t']] fst]].
	split => //; split => //; by exists t''.
rewrite tot_comp; last exact /F2MF_tot.
by exists (t, t').
Qed.

Definition mf_snd S T := (F2MF (@snd S T)).
Arguments mf_snd {S} {T}.

Lemma mfpp_snd (f: S ->> T) (g: S' ->> T') : mf_snd o (f ** g) =~= g o mf_snd|_(dom f \x All).
Proof.
move => s t; rewrite F2MF_comp.
split => [[[[t' t''] [[/= fs1t' gs2t'']]] /=<- _] | [[[t' gs2t'] _] fst]].
	split => //; split => //; by exists t'.
rewrite tot_comp; last exact /F2MF_tot.
by exists (t', t).
Qed.

Lemma mfpp_tight (f: S ->> T) (g: S' ->> T') (f': S ->> T) (g': S' ->> T'):
	f \tightens f' -> g \tightens g' -> (mfpp f g) \tightens (mfpp f' g').
Proof.
rewrite !tight_char.
move => tigh tigh' [s s'] [[t t'] [/=f'st fs't']].
have sfd: s \from_dom f' by exists t.
have [[r fsr] prop] := tigh s sfd.
have s'fd: s' \from_dom g' by exists t'.
have [[r' gsr'] prop'] := tigh' s' s'fd.
split; first by exists (r, r').
move => [q q'] [/= fsq gs'q'].
by split; [apply prop | apply prop'].
Qed.

Definition diag S := fun (d: S) => (d,d).
Arguments diag {S}.
Definition mf_diag S := F2MF (@diag S).
Arguments mf_diag {S}.

Lemma tight_mfpp_diag (f: S ->> T): (mf_diag o f) \tightens ((f ** f) o mf_diag).
Proof.
split.
	rewrite F2MF_comp => s [[t t'] [fst fst']].
	rewrite tot_comp; last exact /F2MF_tot.
	exists (t, t); exists t; split => //.
move => s sfd [_ _] [[t] [fst [<- <-]] _].
by rewrite F2MF_comp /=.
Qed.

Lemma mfpp_diag (f: S ->> T): f \is_singlevalued -> (f ** f) o mf_diag =~= mf_diag o f.
Proof.
rewrite F2MF_comp tot_comp; last exact /F2MF_tot.
move => sing s [t1 t2].
split => [[fst1 fst2] | ]; last by move => [t] [fst [<- <-]].
by exists t1; split => //; rewrite (sing s t2 t1).
Qed.

Lemma mfpp_diag_sing (f: S ->> T): ((f ** f) o mf_diag) \tightens (mf_diag o f) -> f \is_singlevalued.
Proof.
move => tight.
have: ((f ** f) o mf_diag) =~= (mf_diag o f) by apply/tight_equiv/tight_mfpp_diag.
rewrite F2MF_comp tot_comp; last exact /F2MF_tot.
by move => eq s t t'; intros; have /=[ | t'' [fst'' [<- <-]]]//:= (eq s (t, t')).1.
Qed.

Definition mfpp_fun S T S' T' (f: S -> T) (g: S' -> T') := fun p => (f p.1, g p.2).
Notation "f **_f g" := (mfpp_fun f g) (at level 50).

Lemma mfpp_fun_mfpp (f: S -> T) (g: S' -> T'):
	F2MF (f **_f g) =~= (F2MF f) ** (F2MF g).
Proof.
split; rewrite /F2MF /=; first by move <-.
by rewrite /mfpp_fun/mfpp => [[-> ->]]; rewrite -surjective_pairing.
Qed.

Definition ppp1 (fg: (S * S') ->> (T * T')) :=
	make_mf (fun s t => exists s' p, fg (s,s') p /\ p.1 = t).

Definition ppp2 (fg: (S * S') ->> (T * T')) :=
	make_mf (fun s' t' => exists s p, fg (s, s') p /\ p.2 = t').

Lemma ppp1_proj (f: S ->> T) (g: S' ->> T'):
	(exists s', s' \from_dom g) -> ppp1 (f ** g) =~= f.
Proof.
move => [s' [t' gs't']].
by split => [[k [p [[/= eq _] eq']]] | ]; [rewrite -eq' | exists s'; exists (s0, t')].
Qed.

Lemma ppp2_proj (f: S ->> T) (g: S' ->> T'):
	(exists s, s \from_dom f) -> ppp2 (f ** g) =~= g.
Proof.
move => [s [somet fst]].
move => s' t.
by split => [[k [p [[/= _ eq] eq']]] | ]; [rewrite -eq' | exists s; exists (somet, t)].
Qed.

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

Lemma mfpp_dom R Q R' Q' (f: R ->> Q) (g: R' ->> Q'):
  dom (f ** g) === (dom f) \x (dom g).
Proof.
split; last by move => [[s' fs's] [t' ft't]]; exists (s',t').
by move => [] x [] /= fsx gty; split; [exists x.1| exists x.2].
Qed.

Lemma mfpp_inv (f: S ->> T) (g: S' ->> T'):
	(f ** g)\^-1 =~= f\^-1 ** g\^-1.
Proof. done. Qed.

Lemma mfpp_codom (f: S ->> T) (g: S' ->> T'):
  codom (f ** g) === (codom f) \x (codom g).
Proof. by rewrite !codom_dom_inv mfpp_inv -mfpp_dom. Qed.

Lemma mfpp_cotot (f: S ->> T) (g: S' ->> T'):
	f \is_cototal -> g \is_cototal -> (f ** g) \is_cototal.
Proof.
rewrite !cotot_spec.
move => cot cot' [t t'].
have [s fst]:= cot t.
have [s' gs't']:= cot' t'.
by exists (s, s').
Qed.

Lemma mfpp_comp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	(f ** g) o (f' ** g') =~= (f o f') ** (g o g').
Proof.
split => [[] [] fgx [] [] | [] [] [] s1 []]; last first.
	move => fxs1 fs1ffggx H [] [] s2 [] fxs2 fs2ffggx H'.
	split => [ | [] s'1 s'2 [] fs' gs']; first by exists (s1,s2).
	by move: (H s'1 fs') (H' s'2 gs') => [] t' fst [] t'' ; exists (t',t'').
move => fxfgx gxfgx [] ffgxffggx gfgxffggx H.
split; split => [ | s' f'xs]; [by exists fgx.1 | | by exists fgx.2 | ].
	have temp: ((s', fgx.2) \from_dom (f ** g)) by apply: ((H (s', fgx.2))).
	by move: temp => [] [] x1 x2 [] /= fsx1; exists x1.
have temp: ((fgx.1,s') \from_dom (f ** g)) by apply: ((H (fgx.1, s'))).
by move: temp => [] [] x1 x2 [] /= fsx1; exists x2.
Qed.

Lemma mfpp_sing (f: S ->> T) (g: S' ->> T'):
  f \is_singlevalued /\ g \is_singlevalued -> (f ** g) \is_singlevalued.
Proof.
move => [fsing gsing] s t t' [] fst gst [] fst' gst'.
by apply: injective_projections; [apply (fsing s.1)| apply (gsing s.2)].
Qed.

Lemma mfpp_tot (f: S ->> T) (g: S' ->> T'):
	f \is_total /\ g \is_total -> (f ** g) \is_total.
Proof.
by rewrite mfpp_dom; case => -> ->.
Qed.

Lemma tot_mfpp (f: S ->> T) (g: S' ->> T') (s: S) (s': S'):
	(f ** g) \is_total -> f \is_total /\ g \is_total.
Proof.
move => /tot_spec tot; have [[t t' [/= fst gs't']] ]:= tot (s, s').
move/tot_spec: tot; rewrite mfpp_dom => tot.
by apply/ (sprd_All_inv _ _ tot); [exists t; apply fst | exists t'; apply gs't'].
Qed.
End products_sums.
Notation "f '**' g" := (mfpp f g) (at level 50).
Notation "f '**_f' g" := (mfpp_fun f g) (at level 50).
Notation "f '+s+' g" := (mfss f g) (at level 50).
Notation "f '+s+_f' g" := (mfss_fun f g) (at level 50).
Arguments diag {S}.
Arguments mf_diag {S}.
Arguments mf_fst {S} {T}.
Arguments mf_snd {S} {T}.