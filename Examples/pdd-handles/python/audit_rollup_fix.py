"""Daily audit rollup (patched).

Same shape as audit_rollup_bug.py, but after each snapshot we re-open
the snapshot file into a fresh workbook handle and continue from there.
That way the audit pass at the end always writes through a Live handle.

Why no bug: every consumer is followed by a fresh producer for any
handle that still gets used. `excel.save_file_as` consumes `wb` and
returns a Live `snapshot_fo`; we re-open that into a Live `wb` before
handing the FileObj to the upload (which would consume it too); and
the upload uses a separately-created FileObj so the re-opened workbook
stays Live for the post-loop audit pass.
"""
import excel
import datatable
import qactions
import file

SNAPSHOT_EVERY = 100


def run_audit(intake_path: str, audit_code: str) -> None:
    intake_fo = file.create_file(intake_path)
    wb = excel.open_existing_file(file=intake_fo)

    rows = excel.read_range(workbook=wb, sheet="Intake", range_="A2:Z")
    pending = datatable.filter_table(rows, where="status != 'processed'")

    for i, _row in enumerate(pending):
        excel.write_cell(workbook=wb, cell=f"AA{i+2}", value=audit_code)

        if i > 0 and i % SNAPSHOT_EVERY == 0:
            snapshot_fo = excel.save_file_as(workbook=wb, path=f"/tmp/audit-snapshot-{i}.xlsx")
            # save_file_as consumed `wb`; re-open the snapshot as the
            # active workbook before we hand the FileObj to S3 (upload
            # consumes it).
            wb = excel.open_existing_file(file=snapshot_fo)
            upload_fo = file.create_file(f"/tmp/audit-snapshot-{i}.xlsx")
            qactions.amazon_s3.UploadFile(File=upload_fo, key=f"snapshots/{i}")

    # Audit pass: write the rollup total into the (possibly re-opened) workbook.
    excel.write_cell(workbook=wb, cell="A1", value="AUDIT_TOTAL")

    final_fo = excel.save_file_as(workbook=wb, path="/tmp/audit-final.xlsx")
    qactions.amazon_s3.UploadFile(File=final_fo, key="audit/final.xlsx")
