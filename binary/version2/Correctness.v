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
(*   Proof of correctness : both processes will never be in the critic     *)
(*   section at once.                                                      *) 
(***************************************************************************)


Require Import Def.
Require Import Streams.
Require Import SStreams.

Definition exclusion (m : Memo) :=
  match pc m true, pc m false with
  | SC, SC => False
  | _, _ => True
  end.

Definition CorrectTrace := SStream Memo exclusion.

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

Inductive Cycle : Memo -> Prop :=
  | cinit : Cycle initial
  | cst : Cycle (proc true initial)
  | cstt : Cycle (proc true (proc true initial))
  | cstf : Cycle (proc false (proc true initial))
  | csttf : Cycle (proc false (proc true (proc true initial)))
  | csf : Cycle (proc false initial)
  | csft : Cycle (proc true (proc false initial))
  | csff : Cycle (proc false (proc false initial))
  | csfft : Cycle (proc true (proc false (proc false initial)))
  | csfff : Cycle (proc false (proc false (proc false initial))).
 
Hint Resolve cinit cst cstt cstf csttf csf csft csff csfft csfff.

Lemma correct : forall m : Memo, Cycle m -> Oracle -> CorrectTrace.
refine
 (cofix choice  : forall m : Memo, Cycle m -> Oracle -> CorrectTrace :=
    fun (m : Memo) (c : Cycle m) (o : Oracle) =>
    SCons _ _ m _ (choice (proc (hd o) m) _ (tl o))). 
(* 
Realizer protocol.
Program_all.
*)
case c; exact I.
case c; case (hd o); auto with core.
Qed.

(*
Require Extraction.
Write Gofer File "mutex" [correct initial].
*)