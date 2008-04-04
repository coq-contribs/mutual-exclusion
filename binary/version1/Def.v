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
(*  Description of Petersson's algorithm for mutual exclusion of two       *)
(*  processes using co-inductive types.                                    *)
(***************************************************************************)


Require Import Bool.
Require Import Streams.

(* The three states of a given process. *)
 
Inductive Etat : Set :=
  | OUT : Etat
  | DEM : Etat
  | SC : Etat.

(* The shared Memory *)

Record Memo : Set :=  {pc1 : Etat; pc2 : Etat; tour : bool}.

(* Some syntax to make things more readable. *)

(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)


(* A single selector for both program counters. *)

Definition pc (m : Memo) (b : bool) := if b then pc1 m else pc2 m.

(* The assignment instructions for the Memory. *)

Definition update_pc (e : Memo) (b : bool) (v : Etat) :=
  if b then Build_Memo v (pc2 e) (tour e) else Build_Memo (pc1 e) v (tour e).

Definition update_tour (e : Memo) (b : bool) := Build_Memo (pc1 e) (pc2 e) b.

(* The algorithm for mutual exclusion *)

Section States.

Definition Process := Memo -> Memo. 

Variable b : bool.


Definition proc : Process :=
  fun m : Memo =>
  match pc m b with
  | OUT => update_tour (update_pc m b DEM) (negb b)
  | DEM =>
      match pc m (negb b) with
      | OUT => update_pc m b SC
      | DEM => if eqb (tour m) (negb b) then m else update_pc m b SC
      | SC => m
      end
  | SC => update_pc m b OUT
  end.


End States.

(* The initial state of the Memory *)


Definition initial : Memo := Build_Memo OUT OUT false.

Section Scheduler.

(*******************************************************************
   The scheduler choices randomly the process to launch. Randomness
   is represented by an oracle, that is, an infinite sequence 
   of boolean choices.
********************************************************************)

Definition Oracle := Stream bool.
Definition Trace := Stream Memo.

CoFixpoint choix  : (bool -> Process) -> Memo -> Oracle -> Trace :=
  fun (p : bool -> Process) (m : Memo) (o : Oracle) =>
  Cons m (choix p (p (hd o) m) (tl o)).

End Scheduler.

(* The definition of the protocol : just call the scheduler *)

Definition protocol := choix proc.

(****************************************************************************
 The protocol may be "executed" interactivelly using a lazy functional
 language, like Haskell. At each step of the interaction the user enters
 which is the next process to be scheduled, and the program answers
 which is the new state of the memory. This enables to explore the
 space of states.
 ***************************************************************************)

Extraction Language Haskell.
Extraction "Mutex" protocol initial.


(****************************************************************************  
 Pierre Letouzey (07 March 04) 

 What follows is a copy of [choix] and [protocol] functions, that will give 
 a better extraction in Ocaml, since we will extract the [_lazy] and [_force]
 function to the [lazy] and [Lazy.force] constructs of Ocaml. 
 ***************************************************************************)
       
Definition _lazy (a : Trace) := a.
Definition _force (a : Trace) := a.
Extract Inlined Constant _lazy => "lazy".
Extract Inlined Constant _force => "Lazy.force".

CoFixpoint choix2  : (bool -> Process) -> Memo -> Oracle -> Trace :=
  fun (p : bool -> Process) (m : Memo) (o : Oracle) =>
  Cons m (_lazy (_force (choix2 p (p (hd o) m) (tl o)))).

Definition protocol2 := choix2 proc.

Extraction Language Ocaml.
Extraction "mutex" protocol2 initial.