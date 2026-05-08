// EXPECT: pass
//
// Hand-rolled bridge for python/audit_rollup_fix.py. Same single-iteration
// snapshot path as the bug version, but the snapshot's FileObj is
// re-opened into a fresh workbook handle (`wb2`) before being uploaded,
// and the audit pass writes through `wb2`.
program typestate;

file_create_file("intake_fo");
excel_open_existing_file("intake_fo", "wb");
excel_read_range("wb", "rows");
datatable_filter_table("rows", "pending");

// Loop body, snapshot branch fired:
excel_write_cell("wb");
//   snapshot_fo = excel.save_file_as(workbook=wb, ...)
excel_save_file_as("wb", "snapshot_fo");
//   wb = excel.open_existing_file(file=snapshot_fo)   # re-open before upload
excel_open_existing_file("snapshot_fo", "wb2");
//   upload_fo = file.create_file(...)
//   qactions.amazon_s3.UploadFile(File=upload_fo, ...)
file_create_file("upload_fo");
qactions_amazon_s3_UploadFile("upload_fo");

// Audit pass — wb2 is Live.
excel_write_cell("wb2");
excel_save_file_as("wb2", "final_fo");
qactions_amazon_s3_UploadFile("final_fo");
