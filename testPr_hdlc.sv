//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author:
// Date:
//////////////////////////////////////////////////

`define Tx_SC   3'h0
`define Tx_Buff 3'h1
`define Rx_SC   3'h2
`define Rx_Buff 3'h3
`define Rx_Len  3'h4
`define BUFF_SIZE 128


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
    VerifyFCSErrorReceive();
    #5000ns;
    VerifyDroppedFrameReceive();
    #5000ns;
    VerifyNonByteAlignedReceive();
    #5000ns;
    VerifyNormalTransmit();
    #5000ns;
    VerifyAbortTransmit();
    #5000ns;
    VerifyFullTxBuffTransmit();
    #5000ns;

    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    if((TbErrorCnt+uin_hdlc.ErrCntAssertions) > 0) begin
      $display("\n\n*********************************");
      $display("*                               *");
      $display("*                     XX   XX   *");
      $display("*                      XX XX    *");
      $display("*  SIMULATION FAILED!   XXX     *");
      $display("*                      XX XX    *");
      $display("*                     XX   XX   *");
      $display("*                               *");
      $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
      $display("*                               *");
      $display("*********************************\n");
    end
    else begin
      $display("\n\n*********************************");
      $display("*                               *");
      $display("*                            XX *");
      $display("*                           XX  *");
      $display("*  SIMULATION PASSED!   XX XX   *");
      $display("*                        XXX    *");
      $display("*                               *");
      $display("*********************************\n");
    end

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

  task MakeRxStimulus(logic [127:0][7:0] Data, int Size, int NonByteAligned);
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

        if(i==Size-1 && j>2) begin
          if(!NonByteAligned) begin
            @(posedge uin_hdlc.Clk);
            uin_hdlc.Rx = Data[i][j];

            PrevData = PrevData >> 1;
            PrevData[4] = Data[i][j];
          end
        end else begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = Data[i][j];

          PrevData = PrevData >> 1;
          PrevData[4] = Data[i][j];
        end
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
    if(!FCSerr) begin
      ReceiveData[Size]   = FCSBytes[7:0];
      ReceiveData[Size+1] = FCSBytes[15:8];
    end
    else begin
      ReceiveData[Size]   = ~FCSBytes[7:0];
      ReceiveData[Size+1] = ~FCSBytes[15:8];
    end

    //Output data
    data = ReceiveData;

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(`Rx_SC, 8'h20);
    else
      WriteAddress(`Rx_SC, 8'h00);

    //Generate stimulus
    InsertFlagOrAbort(1);

    MakeRxStimulus(ReceiveData, Size + 2, NonByteAligned);

    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3, 0);
    end

    if(Abort)
      InsertFlagOrAbort(0);
    else
      InsertFlagOrAbort(1);

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

    if(Drop) begin
      WriteAddress(`Rx_SC, 8'h22);
      repeat(8)
        @(posedge uin_hdlc.Clk);
    end

  endtask

  
  task ReadTransmittedData(int Size, int Abort, output logic [127:0][7:0] ReadData);
    logic [7:0] Flag, AbortFlag, DataByte, PrevData;
    int i, j, AbortTime;
    Flag = 8'b01111110;
    AbortFlag = 8'b11111110;
    PrevData = '0;
    DataByte = '0;
    i = 0;
    j = 0;
    if(Abort) begin
      AbortTime = ($urandom % (Size-1))+1;
    end else begin
      AbortTime = -1;
    end

    wait(uin_hdlc.Tx_ValidFrame);

    @(posedge uin_hdlc.Clk);

    // Check start flag
    for(int i = 0; i < 8; i++) begin
      @(posedge uin_hdlc.Clk);
      a_CorrectTxOutput: assert (uin_hdlc.Tx == Flag[i]) else begin
          $display("ERROR: TX=%1b, not the correct value in Flag!", uin_hdlc.Tx);
          TbErrorCnt++;
        end
    end

    // Read data
    while (1) begin
      @(posedge uin_hdlc.Clk);
      PrevData = PrevData >> 1;
      PrevData[7] = uin_hdlc.Tx;
      DataByte = DataByte >> 1;
      DataByte[7] = uin_hdlc.Tx;

      // Check for End or Abort flag
      if((PrevData == Flag) || (PrevData == AbortFlag)) begin
        break;
      end

      // Check for zero insertion, stop after frame end or abort
      if(&PrevData[7:3] && uin_hdlc.Tx_ValidFrame && !uin_hdlc.Tx_AbortedTrans) begin
        @(posedge uin_hdlc.Clk);
        PrevData = PrevData >> 1;
        PrevData[7] = uin_hdlc.Tx;
        a_ZeroInsertion: assert (uin_hdlc.Tx == 0) else begin
            $display("ERROR: No zero inserted!");
            TbErrorCnt++;
        end
      end

      i++;
      // Save data byte
      if(i%8 == 0) begin
        ReadData[j] = DataByte;
        j++;
      end

      // Insert Abort signal
      if(j == AbortTime && i%8 == 0) begin
        WriteAddress(`Tx_SC, 8'h04);
      end
    end

  endtask

  task Transmit(int Size, int Abort, output logic [127:0][7:0] WrittenData, output logic [127:0][7:0] TransmittedData, output logic [15:0] FCSBytes);
  logic [7:0]  ReadData;
  string msg;
  if(Abort)
    msg = "- Abort";
  else
    msg = "- Normal";
  $display("*************************************************************");
  $display("%t - Starting task Transmit %s", $time, msg);
  $display("*************************************************************");

  for (int i = 0; i < Size; i++) begin
    WrittenData[i] = $urandom;
  end
  WrittenData[Size]   = '0;
  WrittenData[Size+1] = '0;

  GenerateFCSBytes(WrittenData, Size, FCSBytes);

  //Write to Tx Buffer
  for (int i = 0; i < Size; i++) begin
    @(posedge uin_hdlc.Clk);
    WriteAddress(`Tx_Buff, WrittenData[i]);
  end

  //Verify Tx_Full Asserted
  if(Size >= `BUFF_SIZE-2) begin
    //Wait for signal propagation
    repeat(2)
      @(posedge uin_hdlc.Clk);
    a_TxFullAsserted: assert (uin_hdlc.Tx_Full == 1'b1) $display("PASS: a_TxFullAsserted");
    else begin
      $display("ERROR: Tx_Full=%0b, not asserted after writing 126 bytes or more to TxBuff!", uin_hdlc.Tx_Full);
      TbErrorCnt++;
    end
  end

  //Start transmission and read Tx output
  WriteAddress(`Tx_SC, 8'h02);

  fork
    begin
      ReadTransmittedData(Size+2, Abort, TransmittedData);
    end
    begin
      if(!Abort) begin
        for(int i = 0; i < Size-1; i++) begin
          wait(uin_hdlc.Tx_RdBuff);
          @(posedge uin_hdlc.Clk);
        end
        a_TxDoneAsserted: assert (uin_hdlc.Tx_Done == 1'b1) $display("PASS: a_TxDoneAsserted");
        else begin
          $display("ERROR(%0t): Tx_Done=%0b, not asserted after reading entire TxBuff!", $time, uin_hdlc.Tx_Done);
          TbErrorCnt++;
        end
      end
    end
  join

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
          CheckReg[16]   = CheckReg[16] ^ 1;
        end
        CheckReg = CheckReg >> 1;
      end
    end
    FCSBytes = CheckReg;
  endtask

//----------------------------------------
//---------- Verification tasks ----------
//----------------------------------------

//---------------- Receive ---------------

  task VerifyAbortReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 40;

    Receive( Size, 1, 0, 0, 0, 0, 0, data); //Abort

    ReadAddress(`Rx_SC, ReadData);
    a_abort_RXSC_content: assert (ReadData == 8'b00101000) $display ("PASS: VerifyAbortReceiveRXSC, Rx_SC=%8b", ReadData);
    else begin
      $display("ERROR: RX_SC=%8b, not the correct value after abort receive!", ReadData);
      TbErrorCnt++;
    end

    // Verify length of frame
    ReadAddress(`Rx_Len, ReadData);
    a_RxLen_equal_Size: assert (ReadData == Size) $display ("PASS: a_RxLen_equal_Size, Rx_Len=%0d", ReadData);
    else begin
      $display("ERROR: Rx_Len=%0d, not the correct received frame size!", ReadData);
      TbErrorCnt++;
    end

    // Verify content of Rx_Buff registers
    for(int i=0; i<`BUFF_SIZE; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_abort_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after abort receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask


  task VerifyNormalReceive();
    logic [127:0][7:0] data;
    logic [7:0]  ReadData;
    int Size;
    Size = 10;

    Receive( Size, 0, 0, 0, 0, 0, 0, data); //Normal

    wait(uin_hdlc.Rx_Ready);

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_normal_RXSC_content: assert (ReadData == 8'b00100001) $display ("PASS: VerifyNormalReceiveRXSC, RX_SC=%8b", ReadData);
    else begin
      $display("ERROR: RX_SC=%8b, not the correct value after normal receive!", ReadData);
      TbErrorCnt++;
    end

    // Verify length of frame
    ReadAddress(`Rx_Len, ReadData);
    a_RxLen_equal_Size: assert (ReadData == Size) $display ("PASS: a_RxLen_equal_Size, Rx_Len=%0d", ReadData);
    else begin
      $display("ERROR: Rx_Len=%0d, not the correct received frame size!", ReadData);
      TbErrorCnt++;
    end

    // Verify content of RxBuff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_normal_RxBuff_content: assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after normal receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask


  task VerifyOverflowReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 126;

    Receive(Size, 0, 0, 0, 1, 0, 0, data); //Overflow

    wait(uin_hdlc.Rx_Ready);

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_overflow_RXSC_content: assert (ReadData == 8'b00010001) $display ("PASS: VerifyOverflowReceiveRXSC, RX_SC=%8b", ReadData);
    else begin
      $display("ERROR: RX_SC=%8b, not the correct value after overflow receive!", ReadData);
      TbErrorCnt++;
    end

    // Verify length of frame
    ReadAddress(`Rx_Len, ReadData);
    a_RxLen_equal_Size: assert (ReadData == Size) $display ("PASS: a_RxLen_equal_Size, Rx_Len=%0d", ReadData);
    else begin
      $display("ERROR: Rx_Len=%0d, not the correct received frame size!", ReadData);
      TbErrorCnt++;
    end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_overflow_RxBuff_content: assert (ReadData == data[i]) else begin
        $display("ERROR: RX_BUFF[%0d]=%8b, not the correct value after overflow receive, should be: %8b!", i, ReadData, data[i]);
        TbErrorCnt++;
      end
    end

  endtask

  task VerifyFCSErrorReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 30;

    Receive( Size, 0, 1, 0, 0, 0, 0, data); //FCS Error

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_FCSError_RXSC_content: assert (ReadData == 8'b00100100) $display ("PASS: VerifyFCSErrorReceiveRXSC, RX_SC=%8b", ReadData);
    else begin
      $display("ERROR: RX_SC=%8b, not the correct value after FCS error receive!", ReadData);
      TbErrorCnt++;
    end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_FCSError_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after FCS error receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask

  task VerifyNonByteAlignedReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 2;

    Receive( Size, 0, 0, 1, 0, 0, 0, data); //NonByteAligned

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_NonByteAligned_RXSC_content: assert (ReadData == 8'b00000100) $display ("PASS: VerifyNonByteAlignedRXSC, RX_SC=%8b", ReadData);
    else begin
      $display("ERROR: RX_SC=%8b, not the correct value after non-byte aligned frame receive!", ReadData);
      TbErrorCnt++;
    end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_NonByteAligned_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after non-byte aligned frame receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask

  task VerifyDroppedFrameReceive();
    logic [127:0][7:0] data;
    logic [7:0] ReadData;
    int Size;
    Size = 50;

    Receive( Size, 0, 0, 0, 0, 1, 0, data); //Dropped Frame

    // Verify content of Rx_SC register
    ReadAddress(`Rx_SC, ReadData);
    a_dropped_RXSC_content: assert (ReadData == 8'b00100000) $display ("PASS: VerifyDroppedFrameRXSC, RX_SC=%8b", ReadData);
    else begin
      $display("ERROR: RX_SC=%8b, not the correct value after Dropped frame receive!", ReadData);
      TbErrorCnt++;
    end

    // Verify length of frame
    ReadAddress(`Rx_Len, ReadData);
    a_RxLen_equal_Size: assert (ReadData == Size) $display ("PASS: a_RxLen_equal_Size, Rx_Len=%0d", ReadData);
    else begin
      $display("ERROR: Rx_Len=%0d, not the correct received frame size!", ReadData);
      TbErrorCnt++;
    end

    // Verify content of Rx_Buff registers
    for(int i=0; i<Size; i++) begin
      ReadAddress(`Rx_Buff, ReadData);
      a_dropped_RxBuff_content: assert (ReadData == 0) else begin
        $display("ERROR: RX_BUFF[%0d]=%0b, not the correct value after Dropped frame receive!", i, ReadData);
        TbErrorCnt++;
      end
    end

  endtask

  //---------------- Transmit ---------------

  task VerifyNormalTransmit();
    logic [127:0][7:0] WrittenData;
    logic [127:0][7:0] TransmittedData;
    logic [7:0]  ReadData;
    logic [15:0] FCSBytes;
    int Size;
    Size = 126;

    Transmit( Size, 0, WrittenData, TransmittedData, FCSBytes); //Normal

    wait(uin_hdlc.Tx_Done);

    // Verify Transmitted Data
    for(int i = 0; i < Size; i++) begin
      a_CorrectTxData: assert (TransmittedData[i] == WrittenData[i]) else begin
        $display("ERROR: Tx_Byte[%0d]=%8b, not the correct TX byte value!", i, TransmittedData[i]);
        TbErrorCnt++;
      end
    end

    // Verify FCS Bytes
    a_CorrectTxFCS: assert ({TransmittedData[Size+1], TransmittedData[Size]} == FCSBytes) else begin
      $display("ERROR: Tx_FCS_Bytes=%0h, not the correct FCS value: %0h!", {TransmittedData[Size], TransmittedData[Size+1]}, FCSBytes);
      TbErrorCnt++;
    end

  endtask

  task VerifyAbortTransmit();
    logic [127:0][7:0] WrittenData;
    logic [127:0][7:0] TransmittedData;
    logic [7:0]  ReadData;
    logic [15:0] FCSBytes;
    int Size;
    Size = 64;

    Transmit( Size, 1, WrittenData, TransmittedData, FCSBytes); //Abort

  endtask

  task VerifyFullTxBuffTransmit();
    logic [127:0][7:0] WrittenData;
    logic [127:0][7:0] TransmittedData;
    logic [7:0]  ReadData;
    logic [15:0] FCSBytes;
    int Size;
    Size = 126;

    Transmit( Size, 0, WrittenData, TransmittedData, FCSBytes); //Normal

    // Verify Transmitted Data
    for(int i = 0; i < Size; i++) begin
      a_CorrectTxData: assert (TransmittedData[i] == WrittenData[i]) else begin
        $display("ERROR: Tx_Byte[%0d]=%8b, not the correct TX byte value!", i, TransmittedData[i]);
        TbErrorCnt++;
      end
    end

    // Verify FCS Bytes
    a_CorrectTxFCS: assert ({TransmittedData[Size+1], TransmittedData[Size]} == FCSBytes) else begin
      $display("ERROR: Tx_FCS_Bytes=%0h, not the correct FCS value: %0h!", {TransmittedData[Size], TransmittedData[Size+1]}, FCSBytes);
      TbErrorCnt++;
    end

  endtask

endprogram
