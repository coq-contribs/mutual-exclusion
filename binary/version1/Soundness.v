(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(***************************************************************************)
(*                  MUTUAL EXCLUSION OF TWO PROCESSES                      *)
(*                        (Peterson's algorithm)                           *)
(*                                                                         *)
(*                             Eduardo Gimenez                             *)
(*                                (17/03/97)                               *)
(*                                                                         *)
(***************************************************************************)
(*  Proof of soundness : if both processes are equitably scheduled, then   *)
(*  both will go through the critic section an infinite number of times.   *)
(***************************************************************************)


Require Import Bool.
Require Import Streams.
Require Import Def.

(* The definition of Exists in Streams was changed, this file works *)
(* with the old definition *)
Set Implicit Arguments.
Unset Strict Implicit.
Inductive Exists (A : Set) (P : Stream A -> Prop) : Stream A -> Prop :=
  | Here : forall x : Stream A, P x -> Exists P x
  | Further : forall x : Stream A, ~ P x -> Exists P (tl x) -> Exists P x.

Set Strict Implicit.
Unset Implicit Arguments.

Definition is (b : bool) (x : Oracle) := hd x = b.
Definition in_SC (b : bool) (x : Trace) := pc (hd x) b = SC.
Definition Equity (b : bool) := ForAll (Exists (is b)).


(* Some premliminary lemmas *)

Lemma tl_Equity :
 forall (b : bool) (o : Oracle), Equity b o -> Equity b (tl o).
intros b o H; case H; trivial with bool core.
Qed.
Hint Resolve tl_Equity.

Lemma tl_Exists :
 forall (b : bool) (o : Oracle), Equity b o -> Exists (is b) (tl o).
intros b o H; case H.
intros H0 H1.
case H1.
trivial with bool core.
Qed.
Hint Resolve tl_Exists.

Lemma Equity_project :
 forall (b : bool) (o : Oracle), Equity b o -> Exists (is b) o.
intros b o H.
case H; try trivial with bool core.
Qed.
Hint Resolve Equity_project.


(* The states to be treated *)

Notation st := (proc true initial) (only parsing).
Notation stt := (proc true (proc true initial)) (only parsing).
Notation stf := (proc false (proc true initial)) (only parsing).
Notation sttf := (proc false (proc true (proc true initial))) (only parsing).
Notation sf := (proc false initial) (only parsing).
Notation sft := (proc true (proc false initial)) (only parsing).
Notation sff := (proc false (proc false initial)) (only parsing).
Notation sfft := (proc true (proc false (proc false initial))) (only parsing).
Notation sfff := (proc false (proc false (proc false initial)))
  (only parsing).


Section The_Cycle.

Variable b b1 : bool.
Inductive Cycle : Memo -> Prop :=
  | cf : b1 <> b -> Cycle (proc b1 initial)
  | cff : b1 <> b -> Cycle (proc b1 (proc b1 initial))
  | cfff : b1 <> b -> Cycle (proc b1 (proc b1 (proc b1 initial))).

End The_Cycle.
Hint Resolve cf cff cfff. 

(*************************************************************
   The proof consists in finding a path from each of the 
   possible states to another state that satisfies the
   condition in_SC. Such paths are constructed bottom-up,
   starting from the states where the condition is satisfied.
   Several inductions are needed to avoid getting into infinite
   loops due to non-equitable scheduling. The following lemmas
   construct up the paths for each node. 

 ****************************************************************) 


(* Some useful tacticals *)

Ltac SolveHere := constructor 1; unfold in_SC in |- *; auto with bool core.


Ltac SolveFurther eq :=
  constructor 2;
   [ unfold in_SC in |- *; simpl in |- *; discriminate
   | simpl in |- *; rewrite eq; simpl in |- *; auto with bool ].

Ltac SolveSimpleNode :=
  intros o H; constructor 2;
   [ unfold in_SC in |- *; simpl in |- *; discriminate
   | simpl in |- *; case (hd o); auto with bool core ].

Ltac SolveCycleNode H eq2 :=
  elim H;
   [ unfold is in |- *; intros x theeq; SolveFurther theeq;
      auto with bool datatypes
   | intros x diseq nomatters hypind; SolveFurther (eq2 (hd x));
      auto with bool datatypes ].

Ltac SolveCycleNode1 H :=
  elim H;
   [ unfold is in |- *; intros x theeq; SolveFurther theeq;
      auto with bool datatypes
   | intros x diseq nomatters hypind ].

(* Paths for the first process *)

Lemma fnttf1 :
 forall o : Oracle,
 Exists (in_SC true)
   (protocol (proc false (proc true (proc true initial))) o).
intro b.
 SolveHere.
Qed.
Hint Resolve fnttf1.

Lemma fntf1 :
 forall o : Oracle,
 Exists (is true) o ->
 Exists (in_SC true) (protocol (proc false (proc true initial)) o).
intros o H.
SolveCycleNode H not_true_is_false.
Qed.
Hint Resolve fntf1.

Lemma fntt1 :
 forall o : Oracle,
 Exists (in_SC true) (protocol (proc true (proc true initial)) o).
 SolveHere.
Qed.
Hint Resolve fntt1.


Lemma fnt1 :
 forall o : Oracle,
 Equity true o -> Exists (in_SC true) (protocol (proc true initial) o).
 SolveSimpleNode.
Qed.
Hint Resolve fnt1.

Lemma fnfft1 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 Exists (in_SC true)
   (protocol (proc true (proc false (proc false initial))) o).
intros o1 H.
cut (Equity false o1); auto with bool core.
intros H1.
inversion_clear H1.
generalize H; clear H.
SolveCycleNode H0 not_false_is_true.
Qed.
Hint Resolve fnfft1.

Lemma fnft1 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 Exists (in_SC true) (protocol (proc true (proc false initial)) o).
intros o1 H.
cut (Equity false o1); auto with bool core.
intros H1.
inversion_clear H1.
generalize H; clear H.
SolveCycleNode H0 not_false_is_true.
Qed.
Hint Resolve fnft1.


Lemma fnf1 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 forall m : Memo, Cycle true false m -> Exists (in_SC true) (protocol m o).
simpl in |- *; intros o H.
cut (Equity true o); auto with bool core.
intros H1.
inversion_clear H1.
generalize H; clear H.
elim H0.
unfold is in |- *.
intros x eq H m whichm.
case whichm; SolveFurther eq.
intros x diseq H hypind H1 m whichm.
case whichm; SolveFurther (not_true_is_false (hd x)); auto with bool core.
apply hypind; auto.
apply (cf true false); auto with bool core.
Qed.
Hint Resolve fnf1.


Lemma fninit1 :
 forall o : Oracle,
 (forall b : bool, Equity b o) -> Exists (in_SC true) (protocol initial o).
 SolveSimpleNode.
Qed.
Hint Resolve fninit1.


(* Paths for the second process *)


Lemma fnfft2 :
 forall o : Oracle,
 Exists (in_SC false)
   (protocol (proc true (proc false (proc false initial))) o).
 SolveHere.
Qed.
Hint Resolve fnfft2.

Lemma fnff2 :
 forall o : Oracle,
 Exists (in_SC false) (protocol (proc false (proc false initial)) o).
 SolveHere.
Qed.
Hint Resolve fnff2.

Lemma fnft2 :
 forall o : Oracle,
 Exists (is false) o ->
 Exists (in_SC false) (protocol (proc true (proc false initial)) o).
intros o H.
SolveCycleNode H not_false_is_true.
Qed.
Hint Resolve fnft2.


Lemma fnf2 :
 forall o : Oracle,
 Equity false o -> Exists (in_SC false) (protocol (proc false initial) o).
 SolveSimpleNode. 
Qed.
Hint Resolve fnf2.

Lemma fnttf2 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 Exists (in_SC false)
   (protocol (proc false (proc true (proc true initial))) o).
intros o1 H.
cut (Equity true o1); auto with bool core.
intros H1.
inversion_clear H1.
generalize H; clear H.
SolveCycleNode H0 not_true_is_false.
Qed.
Hint Resolve fnttf2.

Lemma fntf2 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 Exists (in_SC false) (protocol (proc false (proc true initial)) o).
intros o1 H.
cut (Equity true o1); auto with bool core.
intros H1.
inversion_clear H1.
generalize H; clear H.
SolveCycleNode H0 not_true_is_false.
Qed.
Hint Resolve fntf2.


Lemma fntt2 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 forall m : Memo, Cycle false true m -> Exists (in_SC false) (protocol m o).
simpl in |- *; intros o H.
cut (Equity false o); auto with bool core.
intros H1.
inversion_clear H1.
generalize H; clear H.
elim H0.
unfold is in |- *.
intros x eq H m whichm.
case whichm; SolveFurther eq.
intros x diseq H hypind H1 m whichm.
case whichm; SolveFurther (not_false_is_true (hd x)); auto with bool core.
Qed.
Hint Resolve fntt2.

Lemma fninit2 :
 forall o : Oracle,
 (forall b : bool, Equity b o) -> Exists (in_SC false) (protocol initial o).
 SolveSimpleNode. 
Qed.
Hint Resolve fninit2.

Lemma fnfff2 :
 forall o : Oracle,
 (forall b : bool, Equity b o) ->
 Exists (in_SC false)
   (protocol (proc false (proc false (proc false initial))) o).
 SolveSimpleNode. 
apply fntt2; [ auto with bool core | apply (cf false true diff_true_false) ].
Qed.
Hint Resolve fnfff2.

(*************************************************************** 
  The soundness theorem asserts that each of the processes will
   always enter into the critical section once more.
 ***************************************************************)

Definition Soundness (m : Memo) :=
  forall o : Oracle,
  (forall b : bool, Equity b o) ->
  forall id : bool, ForAll (Exists (in_SC id)) (choix proc m o).

Theorem soundness : Soundness initial.
cofix soundness_initial with (soundness_st : Soundness (proc true initial))
 (soundness_stt : Soundness (proc true (proc true initial)))
 (soundness_stf : Soundness (proc false (proc true initial)))
 (soundness_sttf : Soundness (proc false (proc true (proc true initial))))
 (soundness_sf : Soundness (proc false initial))
 (soundness_sft : Soundness (proc true (proc false initial)))
 (soundness_sff : Soundness (proc false (proc false initial)))
 (soundness_sfft : Soundness (proc true (proc false (proc false initial))))
 (soundness_sfff : Soundness (proc false (proc false (proc false initial))));
 (unfold Soundness in soundness_stf; unfold Soundness in soundness_sttf;
   unfold Soundness in soundness_sf; unfold Soundness in soundness_sft;
   unfold Soundness in soundness_sff; unfold Soundness in soundness_sfft;
   unfold Soundness in soundness_sfff; unfold Soundness in soundness_initial;
   unfold Soundness in soundness_st; unfold Soundness in soundness_stt;
   unfold Soundness in |- *; simple destruct id);
 (constructor;
   [ auto with bool core
   | simpl in |- *; case (hd o); (simpl in |- *; auto with bool core) ]).
Qed.
