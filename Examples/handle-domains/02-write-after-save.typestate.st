// EXPECT: fail
// After save-as the original id is Closed; writing through it must fail.
program typestate;
excel_open_existing_file("wb1");
excel_save_file_as("wb1", "wb1.copy");
excel_write_cell("wb1");
