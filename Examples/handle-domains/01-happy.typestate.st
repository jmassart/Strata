// EXPECT: pass
// Happy path: open a workbook, write a cell, save-as into a fresh id.
program typestate;
excel_open_existing_file("wb1");
excel_write_cell("wb1");
excel_save_file_as("wb1", "wb1.copy");
