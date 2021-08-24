package mylib
import spinal.core._
import spinal.core.internals.Operator
import spinal.lib._
import spinal.lib.fsm._

import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.util.Random
import spinal.lib.experimental.math._
import spinal.lib.io.ReadableOpenDrain

import java.io.PrintWriter
import java.io.File
import scala.io.Source
import java.io.StringReader

//**************************************IF************************************//
/* simple adder */
object add{
  def apply(data: => UInt, datb: => UInt): UInt = {data + datb}
}

object sub{
  def apply(data: => UInt, datb: => UInt): UInt = {datb - data}
}

/* mux */
object mux{
  def apply(data: => UInt, datb: => UInt, sel: => Bool): UInt = {sel? data | datb}
}

/* IFID pipeline left  */
case class IFID_left(pc_wid: Int) extends Bundle {
  val pc_reg = out UInt(pc_wid bits)
  val inst   = out UInt(32 bits)
}

/* Rom */
class InstRom (DataWid:Int,DataNum:Int) extends Component{
  val io = new Bundle{
    val en   = in Bool
    val addr = in UInt(log2Up(DataNum) bits)
    val inst = out Bits(DataWid bits)
  }

  def binaryToDecWithOutRecur(src: String): Int = {
    if(!src.matches("[0|1]*")){
      println("invalid input")
      return 0
    }
    val tmp = src.reverse
    var res: Int = 0
    for(i <- 0 to tmp.length - 1){
      res += tmp.substring(i,i+1).toInt * (1 << i)
    }
    res
  }

  val mem   = Mem(Bits(DataWid bits),DataNum)
  val file  = Source.fromFile("rom.bin")
  val list1 = ListBuffer[Bits]()
  var num = 0
  for(line <- file.getLines)
  {
    list1 += binaryToDecWithOutRecur(line)
    num = num + 1
  }
  for(i<- num until DataNum){
    list1 += 0
  }

  mem.init(list1)
  io.inst := mem.readAsync(io.addr)
}

class IF (pc_wid: Int,romDataNum:Int) extends Component{
  val io = new Bundle{
    val PCSrc     = in  Bool
    val branch_pc = in  UInt(pc_wid bits)
    val ID_pc_reg = in  UInt(pc_wid bits)
    val pcwrite   = in  Bool
    val isbranch  = in  Bool
    val test      = out Bool
  }
  val stage_out = new IFID_left(32)

  //pc + 4
  val add4 = add(stage_out.pc_reg,4)

  //inst rom
  val rom   = new InstRom(32,romDataNum)

  //predict buffer & predict target buffer

  val predict_pc      = UInt(pc_wid bits)
  val target_pc       = UInt(pc_wid bits)
  val pc_status       = UInt(2 bits)
  val pc_status_pre   = UInt(2 bits)
  val branch_predict  = Bool
  val Pre_Buffer      = Mem(Bits(32 bits),wordCount = romDataNum).init(List.fill(romDataNum)(1))
  val Pre_tar_Buffer  = Mem(Bits(32 bits),wordCount = romDataNum).init(List.fill(romDataNum)(0))
  val Pre_result      = out Bool

  pc_status :=  Pre_Buffer.readAsync(
    address = io.ID_pc_reg.resize(10)
  ).asUInt.resize(2)

  Pre_Buffer.write(
    enable  = io.isbranch,
    address = io.ID_pc_reg.resize(10),
    data    = io.PCSrc? ((pc_status === 3)? pc_status.asBits | (pc_status + 1).asBits)
                                | ((pc_status === 0)? pc_status.asBits | (pc_status - 1).asBits)
  )

  pc_status_pre :=  Pre_Buffer.readAsync(
    address = stage_out.pc_reg.resize(log2Up(romDataNum))
  ).asUInt.resize(2)

  Pre_tar_Buffer.write(
    enable  = io.PCSrc,
    address = io.ID_pc_reg.resize(10),
    data    = io.branch_pc.asBits
  )

  target_pc   :=  Pre_tar_Buffer.readAsync(
    address = stage_out.pc_reg.resize(log2Up(romDataNum))
  ).asUInt

  Pre_result  :=  !((RegNext(pc_status_pre(1))init(False)) ^ (io.isbranch))
  predict_pc  :=  pc_status_pre(1)? target_pc | add4

  val test_temp     =  Reg(Bool,False)
  test_temp         :=  True
  io.test           :=  test_temp
  rom.io.en         :=  test_temp
  rom.io.addr       :=  stage_out.pc_reg(31 downto 2).resize(log2Up(romDataNum))
  stage_out.inst    :=  rom.io.inst.asUInt
  //stage_out.pc_reg  :=  Pre_result? (RegNextWhen(predict_pc,test_temp && io.pcwrite)init(0)) | io.branch_pc
  //stage_out.pc_reg  :=  (RegNextWhen(Pre_result? predict_pc | io.branch_pc,test_temp && io.pcwrite)init(0))
  stage_out.pc_reg  :=  (RegNextWhen(Pre_result? (io.pcwrite? predict_pc | stage_out.pc_reg) | io.branch_pc,test_temp)init(0))
}

//**************************************ID************************************//
object RType extends SpinalEnum() {
  val ADD_SUB, SLL, SLT, SLTU, XOR, SRL_SRA, OR, AND = newElement()
}
import RType._

case class Decoder_stage(RegNum: Int=32) extends Bundle {
  val wben     = out Bool
  val wbsel       = out Bool //0:reg 1:mem
  val wbaddr   = out UInt(log2Up(RegNum) bits)
  val alusrc      = out Bool
  val func_field  = out UInt(4 bits)
  val aluop       = out UInt(2 bits)
  //val isbranch    = out Bool
  val memen       = out Bool
  val memwrrd     = out Bool
  val addi_inst   = out Bool //TODO
}

case class Register_stage(dataWidth: Int,RegNum: Int=32) extends Bundle{
  val regrddata1    = out UInt(dataWidth bits)
  val regrddata2    = out UInt(dataWidth bits)
  val rs1           = out UInt(log2Up(RegNum) bits)
  val rs2           = out UInt(log2Up(RegNum) bits)
}

case class  Imm_stage(ImmWid:Int) extends Bundle{
  val imm  = out SInt(ImmWid bits)
}

case class IDEX_left(RegNum: Int=32,dataWidth: Int,ImmWid:Int) extends Bundle{
  val pc_reg        = out UInt(32 bits)
  val Register_out  = new Register_stage(dataWidth,RegNum)
  val Decoder_out   = new Decoder_stage(dataWidth)
  val Imm_out       = new Imm_stage(ImmWid)
}

/* decoder imm interface */
class DecodeImm_Int extends Bundle with IMasterSlave{
  val imm = UInt(32 bits)
  override def asMaster(): Unit = {
    out(imm)
  }
}

class RegReadPort(regNum:Int=32) extends Bundle with IMasterSlave {
  val readAddrs = Vec(UInt(log2Up(regNum) bits),2)
  val readDatas = Vec(UInt(32 bits),2)
  val readEns   = Vec(Bool,2)

  override def asMaster(): Unit = {
    in(readDatas)
    out(readAddrs,readEns)
  }
}

class RegWritePort(regNum:Int=32) extends Bundle with IMasterSlave {
  val writeEn   = Bool
  val writeAddr = UInt(log2Up(regNum) bits)
  val writeData = UInt(32 bits)

  override def asMaster(): Unit = {
    out(writeEn,writeAddr,writeData)
  }
}

/* Decoder TODO */
class Decoder(RegNum: Int=32) extends Component{
  val io = new Bundle{
    val inst      = in UInt(32 bits)
    val stage_out = new Decoder_stage(RegNum)
    val regRead   = master(new RegReadPort(RegNum))
    val imm_out   = master(new DecodeImm_Int)
    val isbranch  = out Bool
  }

  val opcode = io.inst(6 downto 0)


  io.stage_out.addi_inst := (io.inst(6 downto 0 )===U"0010011") && (io.inst(14 downto 12)===U"000")

  //operand
  io.regRead.readAddrs(0) := io.inst(19 downto 15)
  io.regRead.readAddrs(1) := io.inst(24 downto 20)
  io.stage_out.wbaddr  := io.inst(11 downto 7)

    //controller alu src
  io.stage_out.func_field := (io.inst(30).asBits ## io.inst(14 downto 12).asBits).asUInt

  switch(opcode){
    is(U"0110011"){
      io.stage_out.alusrc := False
    }
    is(U"0010011"){
      io.stage_out.alusrc := True
    }
    is(U"0100011",U"0000011"){
      io.stage_out.alusrc := True
    }
    default{
      io.stage_out.alusrc := False
    }
  }

  //immediate
  switch(opcode){
    //R
    is(U"0110011"){
      io.imm_out.imm        := io.inst(11 downto 0).resize(32)
      io.isbranch           := False
    }
    is(U"1100011") { //beq
      io.isbranch           := True
      io.imm_out.imm        := (io.inst(31).asBits ## io.inst(7).asBits ##
                                io.inst(30 downto 25).asBits ## io.inst(11 downto 8).asBits).asUInt.resize(32)
    }
    is(U"0100011"){
      io.isbranch           := False
      io.imm_out.imm        :=(io.inst(31 downto 25).asBits ## io.inst(11 downto 7).asBits).asUInt.resize(32)
    }
    is(U"0010011",U"0000011"){ //imm/ld
      io.isbranch           := False
      io.imm_out.imm        := io.inst(31 downto 20).resize(32)
    }
    default{
      io.isbranch           := False
      io.imm_out.imm        := 0
    }
  }

  //mem op
  switch(opcode) {
    is(U"0000011") { //ld
      io.stage_out.memwrrd  := False
      io.stage_out.memen    := True
    }
    is(U"0100011") { //sd
      io.stage_out.memwrrd  := True
      io.stage_out.memen    := True
    }
    default {
      io.stage_out.memwrrd  := False
      io.stage_out.memen    := False
    }
  }

  //alu op
  io.regRead.readEns(0) := True //TODO
  io.regRead.readEns(1) := True //TODO

  switch(opcode){
    is(U"0110011") { //R-type
      io.stage_out.wben     := True
      io.stage_out.wbsel    := False
      io.stage_out.aluop    := U"10"
    }
    is(U"0000011") { //ld
      io.stage_out.wben     := True
      io.stage_out.wbsel    := True
      io.stage_out.aluop    := U"00"
    }
    is(U"0100011") { //sd
      io.stage_out.wben     := False
      io.stage_out.wbsel    := False
      io.stage_out.aluop    := U"00"
    }


    is(U"1100011") { //beq
      io.stage_out.wben     := False
      io.stage_out.wbsel    := False
      io.stage_out.aluop    := U"01"
    }
    default{

      io.stage_out.aluop    := U"00"
      when(io.stage_out.addi_inst){
        io.stage_out.wben  := True
        io.stage_out.wbsel    := False
      }.otherwise{
        io.stage_out.wben  := False
        io.stage_out.wbsel    := False
      }
    }
  }
}

class ImmGen (ImmWid:Int)extends  Component{
  val io = new Bundle {
    val imm_in    = slave(new DecodeImm_Int)
    val stage_out = new Imm_stage(ImmWid)
  }
    val signBit = B(20 bits, default -> io.imm_in.imm(11))
    io.stage_out.imm := (signBit ## io.imm_in.imm(11 downto 0).asBits).asSInt
}

class Register(regNum: Int = 32) extends  Component {
  val stage_out = new Register_stage(32,regNum)
  val readPort  = slave(new RegReadPort)
  val writePort = slave(new RegWritePort)
  val heap      = Vec(Reg(UInt(32 bits)).init(0),regNum)

  readPort.readDatas(0) := 0
  readPort.readDatas(1) := 0

  when(writePort.writeEn){
    heap(writePort.writeAddr) := writePort.writeData
  }
  //use for write back and read the same register
  for(i <- 0 until 2){
    when(writePort.writeEn && readPort.readEns(i) && (writePort.writeAddr === readPort.readAddrs(i))){
      readPort.readDatas(i) := writePort.writeData
    }.elsewhen(readPort.readEns(i)) {
      readPort.readDatas(i) := heap(readPort.readAddrs(i))
    }
  }
  stage_out.regrddata1  :=  readPort.readDatas(0)
  stage_out.regrddata2  :=  readPort.readDatas(1)
  stage_out.rs1         :=  readPort.readAddrs(0)
  stage_out.rs2         :=  readPort.readAddrs(1)
}

object ValueInit{
  def apply[T <: Bundle](gen: => T): Unit = {
      for(i <- gen.elements){
        i._2 match {
          case u:UInt => u := 0
          case b:Bool => b := False
        }
      }
  }
}

class ID(regNum: Int=32, dataWidth: Int, ImmWid: Int) extends Component{
  val io = slave(new RegWritePort(regNum))
  val stage_in    = new IFID_left(32).flip()
  val ID_decoder  = new Decoder(regNum)
  val ID_register = new Register(regNum)
  val ID_imm      = new ImmGen(ImmWid)
  val stage_out   = new IDEX_left(regNum,dataWidth,ImmWid)
  val IDEX_in     = new IDEX_left(regNum,dataWidth,ImmWid).flip()
  val pcwrite     = out Bool
  val IFIDwrite   = out Bool
  val PCSrc       = out Bool
  val isbranch    = out Bool
  val branch_pc   = out UInt(32 bits)
  val branch_op1  = UInt(dataWidth bits)
  val branch_op2  = UInt(dataWidth bits)
  val EXMEM_in    = new EXMEM_left(32).flip()
  val MEMWB_in    = new MEMWB_left(32).flip()
  val forwarda    = UInt(2 bits)
  val forwardb    = UInt(2 bits)
  val hazard_latch = Reg(Bool) init(False)

  forwarda  :=  U"00"
  forwardb  :=  U"00"
  when((ID_register.readPort.readAddrs(0) === EXMEM_in.wbaddr) && (EXMEM_in.wbaddr =/= 0) && EXMEM_in.wben){
    forwarda := U"10"
  }
  when((ID_register.readPort.readAddrs(0) === MEMWB_in.wbaddr) && (MEMWB_in.wbaddr =/= 0) && MEMWB_in.wben){
    forwarda := U"01"
  }
  when((ID_register.readPort.readAddrs(1) === EXMEM_in.wbaddr) && (EXMEM_in.wbaddr =/= 0) && EXMEM_in.wben){
    forwardb := U"10"
  }
  when((ID_register.readPort.readAddrs(1) === MEMWB_in.wbaddr) && (MEMWB_in.wbaddr =/= 0) && MEMWB_in.wben){
    forwardb := U"01"
  }

  switch(forwarda){
    is(U"00") {
      branch_op1 := ID_register.readPort.readDatas(0)
    }
    is(U"01"){
      branch_op1 := mux(MEMWB_in.memrddata,MEMWB_in.aluwb,MEMWB_in.wbsel)
    }
    is(U"10"){
      branch_op1 := EXMEM_in.result
    }
    default{
      branch_op1 := ID_register.readPort.readDatas(0)
    }
  }

  switch(forwardb){
    is(U"00") {
      branch_op2  :=  ID_register.readPort.readDatas(1)
    }
    is(U"01"){
      branch_op2  :=  mux(MEMWB_in.memrddata,MEMWB_in.aluwb,MEMWB_in.wbsel)
    }
    is(U"10"){
      branch_op2  :=  EXMEM_in.result
    }
    default{
      branch_op2  :=  ID_register.readPort.readDatas(1)
    }
  }

  /* branch detect & branch address in ID stage */
  PCSrc     := ID_decoder.io.isbranch && (branch_op1 === branch_op2)  && pcwrite   //TODO now only beq inst
  branch_pc := (ID_imm.io.stage_out.imm(11).asUInt === 0)? //TODO process immediate number
                add(shift(ID_imm.io.stage_out.imm.asUInt).resize(32),stage_in.pc_reg) |
                sub(shift(ID_imm.io.stage_out.imm(10 downto 0).asUInt).resize(32),stage_in.pc_reg)
  isbranch  := ID_decoder.io.isbranch
  pcwrite   :=  True
  IFIDwrite :=  True

  /* hazard detection */
  when(((IDEX_in.Decoder_out.memwrrd === False) && (IDEX_in.Decoder_out.memen) || (ID_decoder.io.isbranch)) //load /alu branch
    && ((IDEX_in.Decoder_out.wbaddr === stage_out.Register_out.rs1)
    || (IDEX_in.Decoder_out.wbaddr === stage_out.Register_out.rs2))){
    hazard_latch := ((IDEX_in.Decoder_out.memwrrd === False) && (IDEX_in.Decoder_out.memen) && (ID_decoder.io.isbranch))
    pcwrite   :=  False
    IFIDwrite :=  False
    ValueInit(stage_out.Decoder_out)
  }.elsewhen(hazard_latch) {
      pcwrite   :=  False
      IFIDwrite :=  False
      hazard_latch := False
      ValueInit(stage_out.Decoder_out)
  }
    .otherwise{
      hazard_latch := False
      stage_out.Decoder_out   := ID_decoder.io.stage_out
  }

  //decoder register connect
  stage_in.inst <> ID_decoder.io.inst
  ID_decoder.io.regRead <> ID_register.readPort

  //decoder immgen connect
  ID_decoder.io.imm_out <> ID_imm.io.imm_in

  //io wrtie_back connect
  io <> ID_register.writePort

  //stage_out
  stage_out.Imm_out       := ID_imm.io.stage_out
  stage_out.Register_out  := ID_register.stage_out
  stage_out.pc_reg        := stage_in.pc_reg
}

//************************** EX **************************//
object shift{
  def apply(data_in: => UInt): UInt ={
    (data_in ## U"0").asUInt
  }
}

object PortConnect{
  def apply[T <: Bundle](Bundle1: => T,Bundle2: => T): Unit = {
    for(i <- Bundle1.elements){
      for(j <- Bundle2.elements){
        if(i._1 == j._1){
          i._2 := j._2
        }
      }
    }
  }
}

case class alu_stage(dataWidth: Int) extends Bundle{
  val iszero    = out Bool
  val result    = out UInt(dataWidth bits)
}

case class EXMEM_left(dataWidth: Int) extends  Bundle{
  //val branch_pc = out UInt(32 bits)
  //val isbranch  = out Bool
  val wben      = out Bool
  val wbsel     = out Bool
  val wbaddr    = out UInt(5 bits)
  //val memaddr = out UInt(32 bits)
  val memdata   = out UInt(dataWidth bits)
  val memen     = out Bool
  val memwrrd   = out Bool
  val iszero    = out Bool
  val result    = out UInt(dataWidth bits)
}

class aluctrl extends Component{
  val io = new Bundle{
    val func_field = in UInt(4 bits)
    val aluop      = in UInt(2 bits)
    val opcode     = out UInt(4 bits)
    val addi_inst  = in Bool //TODO
  }

  io.opcode := 0
  switch(io.aluop){
    is(U"00"){
      io.opcode := U"0010"
    }
    is(U"01"){
      io.opcode := U"0110"
    }
    is(U"10"){
      switch(io.func_field(2 downto 0)){
        is(U"000"){
          when(io.func_field(3)===False){
            io.opcode := U"0010"
          }.otherwise{
            io.opcode := U"0110"
          }
        }
        is(U"111"){
          io.opcode := U"0000"
        }
        is(U"110"){
          io.opcode := U"0001"
        }
      }
    }
    default{//TODO
      when(io.addi_inst){
        io.opcode := U"0010"
      }.otherwise{
        io.opcode := U"0000"
      }
    }
  }
}

/* alu common port */
class alu_op(dataWidth:Int) extends Component{

  val io = new Bundle{
    val en          =   in Bool
    val operanda    =   in UInt(dataWidth bits)
    val operandb    =   in UInt(dataWidth bits)
    val result      =   out UInt(dataWidth bits)
  }
}

/* and opeartion */
class and_op(dataWidth:Int) extends alu_op(dataWidth){
  io.result := io.en? (io.operanda & io.operandb) | 0
}

/* or opeartion */
class or_op(dataWidth:Int) extends alu_op(dataWidth){
  io.result := io.en? (io.operanda | io.operandb) | 0
}

/* add opeartion */
class add_op(dataWidth:Int) extends alu_op(dataWidth){
  io.result := io.en? (io.operanda + io.operandb) | 0
}

/* sub opeartion */
class sub_op(dataWidth:Int) extends alu_op(dataWidth){
  io.result := io.en? (io.operanda - io.operandb) | 0
}

/* alu top */
class alu (dataWidth:Int) extends Component{
  val io = new Bundle{
    val opcode      = in UInt (4 bits)
    val operanda    = in UInt(dataWidth bits)
    val operandb    = in UInt(dataWidth bits)
    val iszero      = out Bool
    val result      = out UInt(dataWidth bits)
  }

  /* operation enable classification */
  val and_en  = Bool.allowOverride
  val or_en   = Bool.allowOverride
  val add_en  = Bool.allowOverride
  val sub_en  = Bool.allowOverride

  /* result classification */
  val result = new Area{
    val and = UInt(dataWidth bits)
    val or  = UInt(dataWidth bits)
    val add = UInt(dataWidth bits)
    val sub = UInt(dataWidth bits)
  }

  and_en  :=  False
  or_en   :=  False
  add_en  :=  False
  sub_en  :=  False

  def alu_en(en:Bool):Unit = {
    and_en  :=  False
    or_en   :=  False
    add_en  :=  False
    sub_en  :=  False
    en      :=  True
  }

  def inst(op: alu_op, en:Bool, result: UInt): Unit = {
    op.io.en <> en
    op.io.operanda <> io.operanda
    op.io.operandb <> io.operandb
    op.io.result <> result
  }

  /* inst child operation */
  val and_inst  = new and_op(dataWidth)
  val or_inst   = new or_op(dataWidth)
  val add_inst  = new add_op(dataWidth)
  val sub_inst  = new sub_op(dataWidth)

  inst(and_inst, and_en,result.and)
  inst(or_inst, or_en,result.or)
  inst(add_inst, add_en,result.add)
  inst(sub_inst, sub_en,result.sub)

  switch(io.opcode){
    is(0) {
      alu_en(and_en)
      io.result := result.and
    }
    is(1) {
      alu_en(or_en)
      io.result := result.or
    }
    is(2) {
      alu_en(add_en)
      io.result := result.add
    }
    is(6) {
      alu_en(sub_en)
      io.result := result.sub
    }
    default{
      io.result := 0
    }
  }
  io.iszero  := (io.result === 0)
}

class EX(dataWidth : Int) extends Component{
  val stage_in    = new IDEX_left(32,32,32).flip()
  val EX_alu      = new alu(32)
  val EX_aluctrl  = new aluctrl
  val stage_out   = new EXMEM_left(dataWidth : Int)
  val EXMEM_in    = new EXMEM_left(32).flip()
  val MEMWB_in    = new MEMWB_left(32).flip()
  val forwarda    = UInt(2 bits)
  val forwardb    = UInt(2 bits)

  //in <> alu ctrl
  stage_in.Decoder_out.func_field <> EX_aluctrl.io.func_field
  stage_in.Decoder_out.aluop <> EX_aluctrl.io.aluop
  stage_in.Decoder_out.addi_inst <> EX_aluctrl.io.addi_inst

  //forwarding unit
  forwarda  :=  U"00"
  forwardb  :=  U"00"
  when((stage_in.Register_out.rs1 === EXMEM_in.wbaddr) && (EXMEM_in.wbaddr =/= 0) && EXMEM_in.wben){
    forwarda := U"10"
  }
  when((stage_in.Register_out.rs1 === MEMWB_in.wbaddr) && (MEMWB_in.wbaddr =/= 0) && MEMWB_in.wben){
    forwarda := U"01"
  }
  when((stage_in.Register_out.rs2 === EXMEM_in.wbaddr) && (EXMEM_in.wbaddr =/= 0) && EXMEM_in.wben){
    forwardb := U"10"
  }
  when((stage_in.Register_out.rs2 === MEMWB_in.wbaddr) && (MEMWB_in.wbaddr =/= 0) && MEMWB_in.wben){
    forwardb := U"01"
  }

  switch(forwarda){
    is(U"00") {
      stage_in.Register_out.regrddata1 <> EX_alu.io.operanda
    }
    is(U"01"){
      mux(MEMWB_in.memrddata,MEMWB_in.aluwb,MEMWB_in.wbsel) <> EX_alu.io.operanda
    }
    is(U"10"){
      EXMEM_in.result <> EX_alu.io.operanda
    }
    default{
      stage_in.Register_out.regrddata1 <> EX_alu.io.operanda
    }
  }

  switch(forwardb){
    is(U"00") {
      mux(stage_in.Imm_out.imm.asUInt,stage_in.Register_out.regrddata2,stage_in.Decoder_out.alusrc) <> EX_alu.io.operandb
      stage_out.memdata   := stage_in.Register_out.regrddata2
    }
    is(U"01"){
      mux(stage_in.Imm_out.imm.asUInt,mux(MEMWB_in.memrddata,MEMWB_in.aluwb,MEMWB_in.wbsel),stage_in.Decoder_out.alusrc) <> EX_alu.io.operandb
      stage_out.memdata   := mux(MEMWB_in.memrddata,MEMWB_in.aluwb,MEMWB_in.wbsel)
    }
    is(U"10"){
      mux(stage_in.Imm_out.imm.asUInt,EXMEM_in.result,stage_in.Decoder_out.alusrc) <> EX_alu.io.operandb
      stage_out.memdata   := EXMEM_in.result
    }
    default{
      mux(stage_in.Imm_out.imm.asUInt,stage_in.Register_out.regrddata2,stage_in.Decoder_out.alusrc) <> EX_alu.io.operandb
      stage_out.memdata   := stage_in.Register_out.regrddata2
    }
  }

  //alu <> alu_ctrl
  EX_aluctrl.io.opcode <> EX_alu.io.opcode

  //stage out
  PortConnect(stage_out,stage_in.Decoder_out)
  PortConnect(stage_out,EX_alu.io)
  //stage_out.branch_pc := add(stage_in.pc_reg,shift(stage_in.Imm_out.imm.asUInt).resize(32))
}

//********************************** MEM **************************//
case class MEMWB_left(dataWid: Int) extends Bundle{
  val memrddata = out UInt(dataWid bits)
  val wben      = out Bool
  val wbsel     = out Bool
  val wbaddr    = out UInt(5 bits)
  val aluwb     = out UInt(dataWid bits)
}

class MEM(dataWid:Int, wordCnt: Int) extends Component{
  //val io = new Bundle{
  //  val PCSrc = out Bool
  //}
  val stage_in  = new EXMEM_left(dataWid).flip()
  val stage_out = new MEMWB_left(dataWid)
  val mem       = Mem(Bits(dataWid bits),wordCount = wordCnt)

  //io.PCSrc := stage_in.isbranch & stage_in.iszero

  mem.write(
    enable  = stage_in.memen & stage_in.memwrrd,
    address = stage_in.result.resize(log2Up(wordCnt)),
    data    = stage_in.memdata.asBits
  )

  stage_out.memrddata := mem.readAsync(
    //enable  = stage_in.memen & !stage_in.memwrrd,
    address = stage_in.result.resize(log2Up(wordCnt))
  ).asUInt

  stage_out.wben    := stage_in.wben
  stage_out.wbsel   := stage_in.wbsel
  stage_out.wbaddr  := stage_in.wbaddr
  stage_out.aluwb   := stage_in.result
}

//******************************** WB ***************************************//

class WB extends Component{
  //val PCSrc     = in Bool
  val regwrite  = master(new RegWritePort)
  val stage_in  = new MEMWB_left(32).flip()

  regwrite.writeEn    := stage_in.wben
  regwrite.writeAddr  := stage_in.wbaddr
  regwrite.writeData  := mux(stage_in.memrddata,stage_in.aluwb,stage_in.wbsel)
}

//********************************* top ***********************************//
class Stage[T <: Bundle](gen: => T) extends Component{
  val en    = in Bool
  val clear = in Bool
  val left:T= gen.flip()
  val right = createOutPort(left)
  def createOutPort(inBundle:Bundle)= {
    new Bundle {
      for(i <- inBundle.elements){
        val a =out (Reg(i._2.clone()))
        a match{
          case s:Bits => s.init(0)
          case b:Bool => b.init(False)
          case u:UInt => u.init(0)
          case t:SInt => t.init(0)
        }
        valCallbackRec(a,i._1)
        when(clear){
          a match{
            case s:Bits => s := 0
            case b:Bool => b := False
            case u:UInt => u := 0
            case t:SInt => t := 0
          }
        }.elsewhen(en){
          a := i._2
        }
      }
    }
  }
}

class top extends Component{
  def Stage(port: => Bundle, sout: => Bundle,sin: => Bundle,en: => Bool,clear: => Bool): Unit = {
    val st =  new Stage(port)
    st.clear <> clear
    st.en <> en
    st.left <> sout
    st.right <> sin
  }

  val IF_stage  = new IF(32,1024)
  val ID_stage  = new ID(32,32,32)
  val EX_stage  = new EX(32)
  val MEM_stage = new MEM(32,1024)
  val WB_stage  = new WB

  val IFID_en = ID_stage.IFIDwrite&&IF_stage.io.test
  //Stage(new IFID_left(32),IF_stage.stage_out,ID_stage.stage_in,IFID_en,ID_stage.PCSrc)//stall
  Stage(new IFID_left(32),IF_stage.stage_out,ID_stage.stage_in,IFID_en,!IF_stage.Pre_result)//stall
  Stage(new IDEX_left(32,32,32).Decoder_out,ID_stage.stage_out.Decoder_out,EX_stage.stage_in.Decoder_out,True,False)
  Stage(new IDEX_left(32,32,32).Register_out,ID_stage.stage_out.Register_out,EX_stage.stage_in.Register_out,True,False)
  Stage(new IDEX_left(32,32,32).Imm_out,ID_stage.stage_out.Imm_out,EX_stage.stage_in.Imm_out,True,False)
  Stage(new EXMEM_left(32),EX_stage.stage_out,MEM_stage.stage_in,True,False)
  Stage(new MEMWB_left(32),MEM_stage.stage_out,WB_stage.stage_in,True,False)

  IF_stage.io.ID_pc_reg := ID_stage.stage_in.pc_reg
  ID_stage.PCSrc <> IF_stage.io.PCSrc
  ID_stage.isbranch <> IF_stage.io.isbranch
  WB_stage.regwrite <> ID_stage.io
  IF_stage.io.pcwrite <> ID_stage.pcwrite
  IF_stage.io.branch_pc :=  ID_stage.branch_pc
  EX_stage.EXMEM_in :=  MEM_stage.stage_in
  EX_stage.MEMWB_in :=  WB_stage.stage_in
  ID_stage.IDEX_in  :=  EX_stage.stage_in
}

object CPU_top {
  def main(args: Array[String]) {
    SpinalVerilog(new top)
  }
}

