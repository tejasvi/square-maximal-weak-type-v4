/-
Copyright (c) 2026 Tejasvi Singh Tomar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tejasvi Singh Tomar
-/
module

/-!
# Certificates for periodic configurations: the checker

A certificate describes a periodic configuration of point masses by exact natural-number data
(coordinates in units `1/Q`, masses in units `1/Dm`), together with

* witness rectangles `[x0, x1] × [y0, y1]` inside the period cell, each with a radius `rho` and an
  explicit list of atoms of total mass at least `4 rho²`, every one of them within sup-distance
  `rho` of every point of the rectangle;
* pieces `[xa, xb) × [ya, yb)`, each inside one witness rectangle, listed in an order (`sep`) that
  makes them pairwise disjoint: consecutive pieces either share their `x`-range and are stacked in
  `y`, or the second one starts at or to the right of the end of the first one.

An atom of the configuration is coded by `9 i + 3 a + b`: atom `i` of the period cell, moved by
`a - 1` horizontal and `b - 1` vertical periods (`a, b < 3`). In the checks every horizontal
coordinate is offset by one period `Px` and every vertical one by `Py`, so that all comparisons are
between natural numbers.

`checkCert c rNum rDen` checks all of this, and that the total area of the pieces divided by the
mass of a period cell is at least `rNum / rDen`. The functions use only `Nat` arithmetic, `Bool` and
structural recursion on lists, so that `decide +kernel` can evaluate them.
-/

@[expose] public section

namespace CenteredMaximal.Periodic

/-- An atom of the period cell: coordinates `(x / Q, y / Q)`, mass `m / Dm`. -/
structure Atom where
  x : Nat
  y : Nat
  m : Nat
deriving Inhabited

/-- A witness rectangle `[x0 / Q, x1 / Q] × [y0 / Q, y1 / Q]` with radius `rho / Q` and the codes of
its atoms (strictly increasing). -/
structure Rect where
  x0 : Nat
  x1 : Nat
  y0 : Nat
  y1 : Nat
  rho : Nat
  codes : List Nat
deriving Inhabited

/-- A piece `[xa / Q, xb / Q) × [ya / Q, yb / Q)` contained in the witness rectangle number `k`. -/
structure Piece where
  xa : Nat
  xb : Nat
  ya : Nat
  yb : Nat
  k : Nat
deriving Inhabited

/-- A certificate: denominators, periods, the atoms of a period cell, witness rectangles, pieces,
and `ellInv`, where `1 / ellInv` is the least witness side. -/
structure Cert where
  Q : Nat
  Dm : Nat
  Px : Nat
  Py : Nat
  ellInv : Nat
  atoms : List Atom
  rects : List Rect
  pieces : List Piece

namespace Cert

/-- The atom number `i` of the period cell, if there is one. -/
def lookup : List Atom → Nat → Option Atom
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, i + 1 => lookup l i

/-- The atom with code `t` lies within `rho` of every point of the rectangle (in offset
coordinates), and the codes are checked to be atoms of the period cell. Returns the total mass of
the atoms with the given codes, or `none` if a check fails. -/
def atomsMass (c : Cert) (r : Rect) : List Nat → Option Nat
  | [] => some 0
  | t :: ts =>
    match lookup c.atoms (t / 9) with
    | none => none
    | some a =>
      let X := a.x + (t % 9 / 3) * c.Px
      let Y := a.y + (t % 3) * c.Py
      if Nat.ble X (r.x0 + c.Px + r.rho) && Nat.ble (r.x1 + c.Px) (X + r.rho) &&
          Nat.ble Y (r.y0 + c.Py + r.rho) && Nat.ble (r.y1 + c.Py) (Y + r.rho) then
        match atomsMass c r ts with
        | none => none
        | some s => some (a.m + s)
      else none

/-- `a < b`, through `Nat.ble`, which the kernel evaluates natively (unlike `Nat.blt`). -/
def lt (a b : Nat) : Bool := Nat.ble (a + 1) b

/-- A list of natural numbers is strictly increasing. -/
def sortedLt : List Nat → Bool
  | a :: b :: l => lt a b && sortedLt (b :: l)
  | _ => true

/-- A witness rectangle is valid: strictly increasing atom codes, every atom within `rho` of every
point of the rectangle, total mass at least `4 rho²` and side `2 rho` at least `1 / ellInv`. -/
def rectOK (c : Cert) (r : Rect) : Bool :=
  sortedLt r.codes && Nat.ble c.Q (2 * r.rho * c.ellInv) &&
    match atomsMass c r r.codes with
    | none => false
    | some s => Nat.ble (4 * r.rho * r.rho * c.Dm) (s * (c.Q * c.Q))

/-- Every witness rectangle is valid. -/
def rectsOK (c : Cert) : List Rect → Bool
  | [] => true
  | r :: rs => rectOK c r && rectsOK c rs

/-- The rectangle number `k`, if there is one. -/
def rectAt : List Rect → Nat → Option Rect
  | [], _ => none
  | r :: _, 0 => some r
  | _ :: rs, k + 1 => rectAt rs k

/-- A piece is nonempty, lies in the period cell and lies in its witness rectangle. -/
def pieceOK (c : Cert) (p : Piece) : Bool :=
  lt p.xa p.xb && Nat.ble p.xb c.Px && lt p.ya p.yb && Nat.ble p.yb c.Py &&
    match rectAt c.rects p.k with
    | none => false
    | some r => Nat.ble r.x0 p.xa && Nat.ble p.xb r.x1 && Nat.ble r.y0 p.ya && Nat.ble p.yb r.y1

/-- The piece `q` comes after the piece `p`: either `q` starts at or to the right of the end of `p`,
or both have the same `x`-range and `q` starts at or above the top of `p`. -/
def sep (p q : Piece) : Bool :=
  Nat.ble p.xb q.xa || (Nat.beq p.xa q.xa && Nat.beq p.xb q.xb && Nat.ble p.yb q.ya)

/-- Every piece is valid and consecutive pieces are in `sep` order. -/
def piecesOK (c : Cert) : List Piece → Bool
  | [] => true
  | [p] => pieceOK c p
  | p :: q :: l => pieceOK c p && sep p q && piecesOK c (q :: l)

/-- The total area of the pieces, in units `1 / Q²`. -/
def area : List Piece → Nat
  | [] => 0
  | p :: l => (p.xb - p.xa) * (p.yb - p.ya) + area l

/-- The total mass of the atoms of the period cell, in units `1 / Dm`. -/
def cellMass : List Atom → Nat
  | [] => 0
  | a :: l => a.m + cellMass l

/-- The certificate is valid and proves the ratio `rNum / rDen`. -/
def checkCert (c : Cert) (rNum rDen : Nat) : Bool :=
  lt 0 c.Q && lt 0 c.Dm && lt 0 c.Px && lt 0 c.Py && lt 0 c.ellInv &&
    lt 0 rDen && lt 0 (cellMass c.atoms) &&
    rectsOK c c.rects && piecesOK c c.pieces &&
    Nat.ble (rNum * (c.Q * c.Q) * cellMass c.atoms) (area c.pieces * c.Dm * rDen)

end Cert

end CenteredMaximal.Periodic
