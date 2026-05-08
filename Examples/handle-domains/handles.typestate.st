// Handles - typestate-modelled handle domains.
//
// Every handle id has:
//   handleStates[id] : state — Live or Closed.
//   domain[id]       : str   — "workbook", "s3", or "" before bound.

program typestate;

service Handles {
  resource Reg {
    states { Live, Closed };
    field handleStates : dict[str, state];
    field domain       : dict[str, str];
    initial {
      handleStates := dict_const(Closed);
      domain       := dict_const("");
    };
  };

  api excel_open_existing_file (id : str)
    before handleStates[id] == Closed;
    transitions handleStates[id] : Closed -> Live;
    after  domain[id] == "workbook";
    after  forall j : str :: (j == id) or (domain[j] == old(domain)[j]);

  // Two-key transition: the `transitions` shorthand handles a single
  // key, so the frame on `handleStates` is spelled out by hand.
  api excel_save_file_as (id : str, newId : str)
    before handleStates[id]    == Live;
    before domain[id]          == "workbook";
    before handleStates[newId] == Closed;
    after  handleStates[id]    == Closed;
    after  handleStates[newId] == Live;
    after  domain[newId] == "workbook";
    after  forall j : str ::
             ((j == id) or (j == newId)) or (handleStates[j] == old(handleStates)[j]);
    after  forall j : str ::
             (j == newId) or (domain[j] == old(domain)[j]);

  api excel_write_cell (id : str)
    before domain[id] == "workbook";
    transitions handleStates[id] : Live -> Live;
    after  forall j : str :: domain[j] == old(domain)[j];

  api s3_upload_file (id : str)
    before domain[id] == "s3";
    transitions handleStates[id] : Live -> Live;
    after  forall j : str :: domain[j] == old(domain)[j];
};
