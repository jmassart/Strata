// EXPECT: fail
// Open a workbook handle then try to upload it through the S3 API —
// a cross-domain confusion that the typestate must reject.
program typestate;
excel_open_existing_file("wb1");
s3_upload_file("wb1");
