// PDD handle domains — four dicts (wb/dt/fo/cl) × {Never, Live, Consumed}.
// API names mirror Python module paths.

program typestate;

service handles {
  resource Reg {
    states { Live, Consumed, Never };
    field wbState : dict[str, state];
    field dtState : dict[str, state];
    field foState : dict[str, state];
    field clState : dict[str, state];
    initial {
      wbState := dict_const(Never);
      dtState := dict_const(Never);
      foState := dict_const(Never);
      clState := dict_const(Never);
    };
  };

  // file.create_file(path) -> FileObj
  api file_create_file (newFo : str)
    transitions foState[newFo] : Never -> Live;
    after forall j : str :: wbState[j] == old(wbState)[j];
    after forall j : str :: dtState[j] == old(dtState)[j];
    after forall j : str :: clState[j] == old(clState)[j];

  // excel.open_existing_file(file=FileObj) -> Workbook
  // The input FileObj is consumed.
  api excel_open_existing_file (srcFo : str, newWb : str)
    transitions foState[srcFo] : Live  -> Consumed;
    transitions wbState[newWb] : Never -> Live;
    after forall j : str :: dtState[j] == old(dtState)[j];
    after forall j : str :: clState[j] == old(clState)[j];

  // excel.read_range(workbook=Workbook, ...) -> DataTable
  // The workbook stays Live (read is non-destructive).
  api excel_read_range (srcWb : str, newDt : str)
    transitions wbState[srcWb] : Live  -> Live;
    transitions dtState[newDt] : Never -> Live;
    after forall j : str :: foState[j] == old(foState)[j];
    after forall j : str :: clState[j] == old(clState)[j];

  // datatable.filter_table(DataTable, where=...) -> DataTable
  // Source DataTable stays Live (filter is non-destructive in this runtime).
  api datatable_filter_table (srcDt : str, newDt : str)
    before dtState[srcDt] == Live;
    transitions dtState[newDt] : Never -> Live;
    after dtState[srcDt] == Live;
    after forall j : str :: wbState[j] == old(wbState)[j];
    after forall j : str :: foState[j] == old(foState)[j];
    after forall j : str :: clState[j] == old(clState)[j];

  // excel.write_cell(workbook=Workbook, ...) — pure consumer, Live -> Live.
  api excel_write_cell (srcWb : str)
    transitions wbState[srcWb] : Live -> Live;
    after forall j : str :: dtState[j] == old(dtState)[j];
    after forall j : str :: foState[j] == old(foState)[j];
    after forall j : str :: clState[j] == old(clState)[j];

  // excel.save_file_as(workbook=Workbook, path=...) -> FileObj
  // The input Workbook is consumed.
  api excel_save_file_as (srcWb : str, newFo : str)
    transitions wbState[srcWb] : Live  -> Consumed;
    transitions foState[newFo] : Never -> Live;
    after forall j : str :: dtState[j] == old(dtState)[j];
    after forall j : str :: clState[j] == old(clState)[j];

  // qactions.amazon_s3.UploadFile(File=FileObj, ...) — consumes the FileObj.
  api qactions_amazon_s3_UploadFile (srcFo : str)
    transitions foState[srcFo] : Live -> Consumed;
    after forall j : str :: wbState[j] == old(wbState)[j];
    after forall j : str :: dtState[j] == old(dtState)[j];
    after forall j : str :: clState[j] == old(clState)[j];
};
