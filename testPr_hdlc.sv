//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

program testPr_hdlc(
  in_hdlc uin_hdlc
);

  int TbErrorCnt;

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    Init();

    //Tests:
    VerifyNormalReceive();
    #5000ns;
    VerifyAbortReceive();
    #5000ns;
    VerifyOverflowReceive();
    #5000ns;

    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    $display("*********************************");
    $display("*                               *");
    $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
    $display("*                               *");
    $display("*********************************");

  end

  task Init();
    uin_hdlc.Clk         =   1'b0;
    uin_hdlc.Rst         =   1'b0;
    uin_hdlc.Address     = 3'b000;
    uin_hdlc.WriteEnable =   1'b0;
    uin_hdlc.ReadEnable  =   1'b0;
    uin_hdlc.DataIn      =     '0;
    uin_hdlc.TxEN        =   1'b1;
    uin_hdlc.Rx          =   1'b1;
    uin_hdlc.RxEN        =   1'b1;

    TbErrorCnt = 0;

    #1000ns;
    uin_hdlc.Rst         =   1'b1;
  endtask

  task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;
  endtask

  task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;
  endtask


/*  task Receive();
    logic [7:0] ReadData;

    //RX flag
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

    ReadAddress(3'b010 , ReadData);
    $display("Rx_SC=%h", ReadData);

  endtask */

//---------- Stimuli tasks ----------

  task InsertFlagOrAbort(int flag);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    if(flag)
      uin_hdlc.Rx = 1'b0;
    else
      uin_hdlc.Rx = 1'b1;
  endtask

  task MakeRxStimulus(logic [127:0][7:0] Data, int Size);
    logic [4:0] PrevData;
    PrevData = '0;
    for (int i = 0; i < Size; i++) begin
      for (int j = 0; j < 8; j++) begin
        if(&PrevData) begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = 1'b0;
          PrevData = PrevData >> 1;
          PrevData[4] = 1'b0;
        end

        @(posedge uin_hdlc.Clk);
        uin_hdlc.Rx = Data[i][j];

        PrevData = PrevData >> 1;
        PrevData[4] = Data[i][j];
      end
    end
  endtask

  task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead, output logic [127:0][7:0] data);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;
    logic   [2:0][7:0] OverflowData;
    string msg;
    if(Abort)
      msg = "- Abort";
    else if(FCSerr)
      msg = "- FCS error";
    else if(NonByteAligned)
      msg = "- Non-byte aligned";
    else if(Overflow)
      msg = "- Overflow";
    else if(Drop)
      msg = "- Drop";
    else if(SkipRead)
      msg = "- Skip read";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Receive %s", $time, msg);
    $display("*************************************************************");

    for (int i = 0; i < Size; i++) begin
      ReceiveData[i] = $urandom;
    end
    ReceiveData[Size]   = '0;
    ReceiveData[Size+1] = '0;

    //Calculate FCS bits;
    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
    ReceiveData[Size]   = FCSBytes[7:0];
    ReceiveData[Size+1] = FCSBytes[15:8];

    //Output data
    data = ReceiveData;

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(3'h2, 8'h20); // RXSC
    else
      WriteAddress(3'h2, 8'h00); // RXSC

    //Generate stimulus
    InsertFlagOrAbort(1);

    MakeRxStimulus(ReceiveData, Size + 2);

    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3);
    end

    if(Abort) begin
      InsertFlagOrAbort(0);
    end else begin
      InsertFlagOrAbort(1);
    end

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

  endtask

  task GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
    logic [23:0] CheckReg;
    CheckReg[15:8]  = data[1];
    CheckReg[7:0]   = data[0];
    for(int i = 2; i < size+2; i++) begin
      CheckReg[23:16] = data[i];
      for(int j = 0; j < 8; j++) begin
        if(CheckReg[0]) begin
          CheckReg[0]    = CheckReg[0] ^ 1;
          CheckReg[1]    = CheckReg[1] ^ 1;
          CheckReg[13:2] = CheckReg[13:2];
          CheckReg[14]   = CheckReg[14] ^ 1;
          CheckReg[15]   = CheckReg[15];
          CheckReg[16]   = CheckReg[16] ^1;
        end
        CheckReg = CheckReg >> 1;
      end
    end
    FCSBytes = CheckReg;
  endtask

//---------- Assertion tasks ----------

  task VerifyAbortReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 40;

    Receive( Size, 1, 0, 0, 0, 0, 0, data); //Abort

    ReadAddress(3'h2, ReadData);
    a_abort_RXSC_content: assert (ReadData == 8'b00101000) $display ("PASS: VerifyAbortReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after abort receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size+2; i++) begin
      ReadAddress(3'h3, ReadData);
      assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after abort receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask


  task VerifyNormalReceive();
    logic [127:0][7:0] data;
    logic [7:0]  ReadData;
    logic [15:0] FCSBytes;
    int Size;
    Size = 10;

    Receive( Size, 0, 0, 0, 0, 0, 0, data); //Normal

    wait(uin_hdlc.Rx_Ready);

    // Verify content of Rx_SC register
    ReadAddress(3'h2, ReadData);
    a_normal_RXSC_content: assert (ReadData == 8'b00100001) $display ("PASS: VerifyNormalReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after normal receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(3'h3, ReadData);
      assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after normal receive!", i, ReadData);
        TbErrorCnt++;
      end
    end
    for(int i=0; i<(126-Size); i++) begin
      ReadAddress(3'h3, ReadData);
      assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after normal receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

    // Verify CRC Bytes
    ReadAddress(3'h3, ReadData);
    assert (ReadData == data[Size]) else begin
      $display("ERROR: first FCS byte=%8b, not the correct value after normal receive, should be: %8b", ReadData, data[Size]);
      TbErrorCnt++;
    end
    ReadAddress(3'h3, ReadData);
    assert (ReadData == data[Size+1]) else begin
      $display("ERROR: second FCS byte=%8b, not the correct value after normal receive, should be: %8b!", ReadData, data[Size+1]);
      TbErrorCnt++;
    end

  endtask


  task VerifyOverflowReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 126;

    Receive(Size, 0, 0, 0, 1, 0, 0, data); //Overflow

    wait(uin_hdlc.Rx_Ready);

    ReadAddress(3'h2, ReadData);
    a_overflow_RXSC_content: assert (ReadData == 8'b00010001) $display ("PASS: VerifyOverflowReceiveRXSC, RX_SC=%8b", ReadData);
        else begin
          $display("ERROR: RX_SC=%8b, not the correct value after overflow receive!", ReadData);
          TbErrorCnt++;
        end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(3'h3, ReadData);
      assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after overflow receive, should be: %8b!", i, ReadData, data[i]);
        TbErrorCnt++;
      end
    end

  endtask

endprogram
