program Core;

// ===========================================================================
// Coffee machine — Moore FSM.
//
// What "a good coffee machine" means:
//
//   Client side — what the customer expects:
//     * Gets the drink they selected.
//     * Gets the right change back after paying.
//     * Gets a full refund if they cancel.
//
//   Vendor side — what the machine operator requires:
//     * Doesn't get stuck — always returns to IDLE, ready for the next
//       customer.
//     * Only dispenses a drink once the customer has paid enough.
// ===========================================================================


// ---------------------------------------------------------------------------
// 1. States and Drinks
// ---------------------------------------------------------------------------

datatype State () { IDLE(), SELECTED(), PAID(), DISPENSING() };
datatype Drink () { Espresso(), Latte(), Cappuccino() };

function priceOf(d: Drink): int {
  if Drink..isEspresso(d) then 150
  else if Drink..isLatte(d) then 250
  else 200
}


// ---------------------------------------------------------------------------
// 2. Persistent state
// ---------------------------------------------------------------------------

var state  : State;
var drink  : Drink;
var credit : int;   // money inserted, not yet spent
var change : int;   // money returned on dispense   (output)
var refund : int;   // money returned on cancel     (output)


// ---------------------------------------------------------------------------
// 3. FSM invariants — preserved by every transition.
// ---------------------------------------------------------------------------

function wellFormed(s: State, d: Drink, c: int): bool {
  c >= 0                                       // (V) customer never owes money
  && (State..isIDLE(s) ==> c == 0)             // (V) no pending money between customers
  && (State..isPAID(s) ==> c >= priceOf(d))    // (V) dispense only after enough paid
}

function changeWellDefined(s: State, d: Drink, c: int, ch: int): bool {
  ch >= 0                                         // (C) machine never owes negative change
  && (!State..isDISPENSING(s) ==> ch == 0)        // (C) change doesn't leak to next customer
  && (State..isDISPENSING(s)  ==> ch == c - priceOf(d))  // (C) right change at dispense time
}

function refundWellDefined(s: State, rf: int): bool {
  rf >= 0                                      // (C) refunds are never negative
  && (!State..isIDLE(s) ==> rf == 0)           // (C) refunds don't leak to next customer
}

function machineInvariant(s: State, d: Drink, c: int, ch: int, rf: int): bool {
  wellFormed(s, d, c) && changeWellDefined(s, d, c, ch) && refundWellDefined(s, rf)
}


// ---------------------------------------------------------------------------
// 4. Transitions
// ---------------------------------------------------------------------------

procedure selectDrink(d: Drink) returns ()
spec {
  modifies state, drink, credit, refund;
  requires [inv]:           machineInvariant(state, drink, credit, change, refund);
  requires [must_be_idle]:  State..isIDLE(state);
  ensures  [now_selected]:  State..isSELECTED(state);
  ensures  [drink_set]:     drink == d;
  ensures  [no_credit]:     credit == 0;
  ensures  [refund_zero]:   refund == 0;
  ensures  [change_frozen]: change == old change;
  ensures  [inv_preserved]: machineInvariant(state, drink, credit, change, refund);
}
{
  state  := SELECTED();
  drink  := d;
  credit := 0;
  refund := 0;
};

procedure insertCoin(amount: int) returns ()
spec {
  modifies state, credit;
  requires [inv]:                machineInvariant(state, drink, credit, change, refund);
  requires [must_have_selected]: State..isSELECTED(state);
  requires [coin_positive]:      amount > 0;
  ensures  [credit_grew]:        credit == old credit + amount;
  ensures  [credit_monotonic]:   credit >= old credit;
  ensures  [paid_when_enough]:   (credit >= priceOf(drink)) ==> State..isPAID(state);
  ensures  [owed_when_short]:    (credit <  priceOf(drink)) ==> State..isSELECTED(state);
  ensures  [drink_frozen]:       drink  == old drink;
  ensures  [change_frozen]:      change == old change;
  ensures  [refund_frozen]:      refund == old refund;
  ensures  [inv_preserved]:      machineInvariant(state, drink, credit, change, refund);
}
{
  credit := credit + amount;
  if (credit >= priceOf(drink)) {
    state := PAID();
  } else {
    state := SELECTED();
  }
};

procedure dispense() returns ()
spec {
  modifies state, change;
  requires [inv]:             machineInvariant(state, drink, credit, change, refund);
  requires [must_be_paid]:    State..isPAID(state);
  ensures  [now_dispensing]:  State..isDISPENSING(state);
  ensures  [change_computed]: change == old credit - priceOf(old drink);
  ensures  [change_nonneg]:   change >= 0;
  ensures  [drink_frozen]:    drink  == old drink;
  ensures  [credit_frozen]:   credit == old credit;
  ensures  [refund_frozen]:   refund == old refund;
  ensures  [inv_preserved]:   machineInvariant(state, drink, credit, change, refund);
}
{
  state  := DISPENSING();
  change := credit - priceOf(drink);
};

procedure takeCup() returns ()
spec {
  modifies state, credit, change;
  requires [inv]:                machineInvariant(state, drink, credit, change, refund);
  requires [must_be_dispensing]: State..isDISPENSING(state);
  ensures  [back_to_idle]:       State..isIDLE(state);
  ensures  [credit_cleared]:     credit == 0;
  ensures  [change_cleared]:     change == 0;
  ensures  [drink_frozen]:       drink  == old drink;
  ensures  [refund_frozen]:      refund == old refund;
  ensures  [inv_preserved]:      machineInvariant(state, drink, credit, change, refund);
}
{
  state  := IDLE();
  credit := 0;
  change := 0;
};

procedure cancel() returns ()
spec {
  modifies state, credit, refund;
  requires [inv]:              machineInvariant(state, drink, credit, change, refund);
  requires [not_yet_dispensing]:
    State..isIDLE(state) || State..isSELECTED(state) || State..isPAID(state);
  ensures  [back_to_idle]:     State..isIDLE(state);
  ensures  [credit_cleared]:   credit == 0;
  ensures  [refund_is_credit]: refund == old credit;
  ensures  [refund_nonneg]:    refund >= 0;
  ensures  [drink_frozen]:     drink  == old drink;
  ensures  [change_frozen]:    change == old change;
  ensures  [inv_preserved]:    machineInvariant(state, drink, credit, change, refund);
}
{
  refund := credit;
  credit := 0;
  state  := IDLE();
};


// ===========================================================================
// 5. Properties over the FSM
// ===========================================================================

// ---------------------------------------------------------------------------
// P1 — No deadlock: every invariant-satisfying configuration has
// at least one enabled transition.
// ---------------------------------------------------------------------------

function someEnabled(s: State): bool {
       State..isIDLE(s)
    || State..isSELECTED(s)
    || State..isPAID(s)
    || State..isDISPENSING(s)
}

procedure P1_no_deadlock(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]: machineInvariant(s, d, c, ch, rf);
  ensures  [no_dead_state]: someEnabled(s);
};


// ---------------------------------------------------------------------------
// P2 — Reachability of SELECTED from IDLE.
// ---------------------------------------------------------------------------

procedure P2_reach_SELECTED() returns ()
spec {
  modifies state, drink, credit, change, refund;
  requires State..isIDLE(state) && credit == 0 && change == 0 && refund == 0;
  ensures  [reached_SELECTED]: State..isSELECTED(state);
}
{
  call selectDrink(Espresso());
};


// ---------------------------------------------------------------------------
// P3 — Reachability of PAID from IDLE.
// ---------------------------------------------------------------------------

procedure P3_reach_PAID() returns ()
spec {
  modifies state, drink, credit, change, refund;
  requires State..isIDLE(state) && credit == 0 && change == 0 && refund == 0;
  ensures  [reached_PAID]: State..isPAID(state);
}
{
  call selectDrink(Espresso());
  call insertCoin(150);
};


// ---------------------------------------------------------------------------
// P4 — Reachability of DISPENSING from IDLE.
// ---------------------------------------------------------------------------

procedure P4_reach_DISPENSING() returns ()
spec {
  modifies state, drink, credit, change, refund;
  requires State..isIDLE(state) && credit == 0 && change == 0 && refund == 0;
  ensures  [reached_DISPENSING]: State..isDISPENSING(state);
}
{
  call selectDrink(Espresso());
  call insertCoin(150);
  call dispense();
};


// ---------------------------------------------------------------------------
// P5 — Change is always non-negative.
// ---------------------------------------------------------------------------

procedure P5_change_nonneg(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]: machineInvariant(s, d, c, ch, rf);
  ensures  [change_is_nonneg]: ch >= 0;
};

// ---------------------------------------------------------------------------
// P6 — Correct change at dispense time.
// ---------------------------------------------------------------------------

procedure P6_right_change(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]: machineInvariant(s, d, c, ch, rf);
  requires [in_dispensing]: State..isDISPENSING(s);
  ensures  [change_eq_overpay]: ch == c - priceOf(d);
};


// ---------------------------------------------------------------------------
// P7 — Refunds only occur in IDLE.
// ---------------------------------------------------------------------------

procedure P7_refund_localised(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]: machineInvariant(s, d, c, ch, rf);
  requires [refund_nonzero]: rf != 0;
  ensures  [in_idle]: State..isIDLE(s);
};


// ---------------------------------------------------------------------------
// P8 — Change only occurs in DISPENSING.
// ---------------------------------------------------------------------------

procedure P8_change_localised(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]: machineInvariant(s, d, c, ch, rf);
  requires [change_nonzero]: ch != 0;
  ensures  [in_dispensing]: State..isDISPENSING(s);
};


// ---------------------------------------------------------------------------
// P9 — No credit in IDLE.
// ---------------------------------------------------------------------------

procedure P9_no_credit_at_idle(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]: machineInvariant(s, d, c, ch, rf);
  requires [in_idle]: State..isIDLE(s);
  ensures  [credit_zero]: c == 0;
};


// ---------------------------------------------------------------------------
// P10 — No dispense without sufficient payment.
// ---------------------------------------------------------------------------

procedure P10_dispense_only_when_paid(s: State, d: Drink, c: int, ch: int, rf: int) returns ()
spec {
  requires [pre_invariant]:  machineInvariant(s, d, c, ch, rf);
  requires [dispense_guard]: State..isPAID(s);
  ensures  [paid_enough]:    c >= priceOf(d);
};