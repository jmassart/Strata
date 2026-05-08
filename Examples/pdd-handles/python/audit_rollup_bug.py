"""Daily audit rollup.

Reads the day's intake spreadsheet, drops rows already marked
processed, stamps the rest with today's audit code, and snapshots
the workbook every SNAPSHOT_EVERY rows for crash recovery. After
the per-row pass, an audit pass appends a final summary row
("AUDIT_TOTAL") and uploads the result to S3.

Bug: `excel.save_file_as` consumes its workbook handle. On any path
where the conditional snapshot fired (i % SNAPSHOT_EVERY == 0 with
i > 0), `wb` — and its alias `summary_handle` — is left Consumed.
The post-loop `excel.write_cell(workbook=summary_handle, ...)`
requires a Live workbook and rejects.
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

    # Aliased for readability in the audit pass below — same handle.
    summary_handle = wb

    snapshot_path = None
    for i, _row in enumerate(pending):
        excel.write_cell(workbook=wb, cell=f"AA{i+2}", value=audit_code)

        if i > 0 and i % SNAPSHOT_EVERY == 0:
            snapshot_path = f"/tmp/audit-snapshot-{i}.xlsx"
            snapshot_fo = excel.save_file_as(workbook=wb, path=snapshot_path)
            qactions.amazon_s3.UploadFile(File=snapshot_fo, key=f"snapshots/{i}")

    # Audit pass: write the rollup total into the same workbook.
    excel.write_cell(workbook=summary_handle, cell="A1", value="AUDIT_TOTAL")

    final_fo = excel.save_file_as(workbook=summary_handle, path="/tmp/audit-final.xlsx")
    qactions.amazon_s3.UploadFile(File=final_fo, key="audit/final.xlsx")