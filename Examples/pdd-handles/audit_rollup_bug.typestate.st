// EXPECT: fail
//
// Hand-rolled bridge for python/audit_rollup_bug.py.
// Loops unrolled to a single representative path: the path on which
// the conditional snapshot fired exactly once. On that path `wb` is
// Consumed by `excel_save_file_as`, so the post-loop `excel_write_cell`
// rejects.
program typestate;

// intake_fo = file.create_file(intake_path)
file_create_file("intake_fo");
// wb = excel.open_existing_file(file=intake_fo)
excel_open_existing_file("intake_fo", "wb");
// rows = excel.read_range(workbook=wb, ...)
excel_read_range("wb", "rows");
// pending = datatable.filter_table(rows, ...)
datatable_filter_table("rows", "pending");

// Loop body, snapshot branch fired:
//   excel.write_cell(workbook=wb, ...)
excel_write_cell("wb");
//   snapshot_fo = excel.save_file_as(workbook=wb, ...)
excel_save_file_as("wb", "snapshot_fo");
//   qactions.amazon_s3.UploadFile(File=snapshot_fo, ...)
qactions_amazon_s3_UploadFile("snapshot_fo");

// Audit pass: BUG — wb is now Consumed (summary_handle aliases wb).
// excel.write_cell(workbook=summary_handle, ...)
excel_write_cell("wb");
