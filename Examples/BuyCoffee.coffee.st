// TO RUN :
// lake exe strata verify --vc-directory vcs/coffee Examples/BuyCoffee.coffee.st
//
// Menu:
//   espresso   150
//   latte      250
//   cappuccino 200

program Coffee;

// -------- Happy paths --------

program good_espressoExact {
  select espresso;
  pay 150;
  dispense;
  take_cup;
};

program good_latteOverpaid {
  select latte;
  pay 100;
  pay 200;
  dispense;
  take_cup;
};

program good_cappuccinoManyCoins {
  select cappuccino;
  pay 50;
  pay 50;
  pay 50;
  pay 50;
  dispense;
  take_cup;
};

program good_bigOverpay {
  select latte;
  pay 1000;
  dispense;
  take_cup;
};

program good_cancelAfterSelect {
  select latte;
  cancel;
};

program good_cancelMidway {
  select latte;
  pay 100;
  cancel;
};

program good_cancelAfterPaid {
  select espresso;
  pay 200;
  cancel;
};

program good_reselect {
  select latte;
  pay 50;
  cancel;
  select cappuccino;
  pay 200;
  dispense;
  take_cup;
};

program good_twoCustomers {
  select espresso;
  pay 150;
  dispense;
  take_cup;
  select cappuccino;
  pay 200;
  dispense;
  take_cup;
};

// -------- Illegal traces --------

program bad_payFirst {
  pay 150;
  select espresso;
};

program bad_justDrink {
  select espresso;
  dispense;
};

program bad_dispenseUnpaid {
  select latte;
  dispense;
};

program bad_takeEmptyCup {
  select espresso;
  pay 150;
  take_cup;
};

program bad_payAfterPaid {
  select espresso;
  pay 150;
  pay 50;
};

program bad_cancelWhileDispensing {
  select espresso;
  pay 150;
  dispense;
  cancel;
};

program bad_doubleSelect {
  select espresso;
  select latte;
};

program bad_dispenseTwice {
  select espresso;
  pay 150;
  dispense;
  dispense;
};

program bad_underpay {
  select latte;
  pay 100;
  dispense;
};

program bad_takeCupIdle {
  take_cup;
};
