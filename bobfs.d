import std.algorithm;
import std.bitmanip;
import std.exception;
import std.conv;
import std.ascii;
import std.mmfile;
import std.stdio;
import std.traits;
import core.exception;


//	General configuration

const BLOCK_SIZE = 4096;
const N_DIRECT = 10;
const N_IND_SINGLE = 1;

alias Magic = uint;
const Magic MAGIC = 0xb0b0b0b0;


void debugLog(A...)(A args) @trusted {
    stderr.writeln("debug: ", args);
}


//	Basic types & procedures

alias BlockAddr = ulong;
alias DiskSize = ulong;

const BlockAddr NO_BLOCK = 0;

struct AbsAddr {
    BlockAddr blk = NO_BLOCK;
    ulong index;

    invariant { assert (index < BLOCK_SIZE); }

    bool isNull() pure nothrow { return (blk == NO_BLOCK); }
}

ulong numBlocks(DiskSize size, DiskSize blockSize = BLOCK_SIZE) pure nothrow {
    auto nb = size / blockSize;
    if (size % blockSize)
	nb++;
    return nb;
}


//	Serialization/Deserialization on disk

// Scalar arithmetic types are directly written/read.  Composite types
// map the same read/write function over the sequence of their
// members.

void memberMap(alias Fun, T)(ref T obj)
{
    static if (__traits(isArithmetic, T)) {
	Fun(obj);

    } else static if (__traits(isPOD, T)) {
	static if (__traits(hasMember, T, "tupleof"))
	    foreach (ref m; obj.tupleof)
		memberMap!Fun(m);
	else
	    foreach (ref m; obj)
		memberMap!Fun(m);

    } else {
	pragma(msg, "Type `", T, "` is not serializable");
	static assert(false);
    }
}

void diskWrite(B, T)(B blk, ref const T obj) {
    memberMap!((x) => blk.write(x))(obj);
}

void diskReadTo(B, T)(B blk, ref T obj) {
    memberMap!((ref x) => blk.read(x))(obj);
}

auto diskRead(T, B)(B blkdev) {
    T ret;
    blkdev.diskReadTo(ret);
    return ret;
}

struct BlockWriteCache(D, T) {
    T content;
    D dev;
    BlockAddr addr;
    bool dirty = false;

    this(D dev) {
	this.dev = dev;
	this.content = T();
	this.addr = 0;
    }

    void set(BlockAddr addr) {
	if (this.addr == addr)
	    return;

	debugLog("BlockWriteCache: set to ", addr, " (was ", this.addr, ")");
	if (this.addr != 0 && this.dirty) {
	    dev.block(this.addr).diskWrite(this.content);
	}

	this.addr = addr;
	this.dirty = false;

	if (this.addr != 0) {
	    debugLog("reading ", typeid(T), " from blk ", this.addr);
	    this.content = this.dev.block(addr).diskRead!T();
	} else
	    this.content = T();
    }

    ~this() { this.set(0); }
}

//	Disk data types
struct FreeBlock {
    BlockAddr next;
}

struct INodeBlock {
    INode inodes[BLOCK_SIZE / INode.sizeof];
}

struct IndexBlock {
    BlockAddr indices[BLOCK_SIZE / BlockAddr.sizeof];
}

struct DirHdr {
    uint nNameBlocks;
}

struct NameTableEntry {
    AbsAddr addr;

    bool isValid() pure nothrow {
	return ( ! this.isDeleted() && ! this.isEmpty() );
    }

    bool isDeleted() pure nothrow {
	return (addr.blk == 0 && addr.index == 1);
    }

    bool isEmpty() pure	nothrow {
	return (addr.blk == 0 && addr.index == 0);
    }

    void setEmpty() {
	addr.blk = 0;
	addr.index = 0;
	assert (addr.isNull);
    }

    void setDeleted() {
	addr.blk = 0;
	addr.index = 1;
	assert (addr.isNull);
    }
}

struct NameTableBlock {
    NameTableEntry entries[BLOCK_SIZE / NameTableEntry.sizeof];
}

struct DEntryHdr {
    AbsAddr inodeAddr;
    byte nameLen;

    invariant { assert (nameLen >= 0 || nameLen == -1); }

    bool isValid() pure nothrow { return (nameLen != -1); }
    void makeInvalid() { nameLen = -1; }
}

static assert (BLOCK_SIZE % 8 == 0);
const DENTRIES_PER_BLOCK = BLOCK_SIZE * 8 / 33;
const DENTRY_FRAG_ALIGN = 4;
struct DEntryBlock {
    ubyte bitmapBuf[DENTRIES_PER_BLOCK / 8];
    ubyte fragBuf[DENTRIES_PER_BLOCK * 4];
}

// Not a disk structure, memory-only.
struct DEntry {
    AbsAddr inodeAddr;
    string name;
    invariant { assert (name.length <= 255); }
}

static assert (DEntryBlock.sizeof <= BLOCK_SIZE);

enum INodeType { File, Directory }

struct INode {
    INodeType type;
    AbsAddr nextFree;
    DiskSize  size;   // file/directory size in bytes
    BlockAddr direct[N_DIRECT];
    BlockAddr isingle[N_IND_SINGLE];

    // valid only for directories
    DirHdr dirHdr;
}

struct Superblock {
    Magic magic;
    DiskSize volumeSize;
    BlockAddr firstFree;
    AbsAddr freeINode;
    AbsAddr rootINode;
}


//	Utilites & abstractions

enum FSError {
    DiskFull,
    NoEntry,
}

string message(FSError err) pure nothrow {
    final switch(err) {
    case FSError.DiskFull: return "No space left on device";
    case FSError.NoEntry: return "No such file or directory";
    }
}

class FSException : Exception {
    const FSError error;

    this(FSError error) {
	super(error.message);
	this.error = error;
    }
}


auto dataBlocksAddr(D)(const INode* inode, D dev) {
    struct BlockGetter {
	const(INode)* inode;
	D device;

	this(const INode *inode, D dev) {
	    this.inode = inode;
	    this.device = dev;
	}

	BlockAddr opIndex(ulong index) {
	    if (index < N_DIRECT)
		return this.inode.direct[index];

	    index -= N_DIRECT;
	    auto index1 = index / IndexBlock.indices.length;
	    auto index2 = index % IndexBlock.indices.length;

	    if (index1 >= N_IND_SINGLE)
		throw new RangeError();

	    auto indexBlk = dev.block(inode.isingle[index1]).diskRead!IndexBlock();
	    return indexBlk.indices[index2];
	}
    }

    return BlockGetter(inode, dev);
}

//	Procedures

BlockAddr popFreeBlock(D)(D dev) {
    auto sb = dev.block(0).diskRead!Superblock();
    auto freeAddr = sb.firstFree;
    if (freeAddr == NO_BLOCK)
	throw new FSException(FSError.DiskFull);

    auto blk = dev.block(freeAddr).diskRead!FreeBlock();
    sb.firstFree = blk.next;
    dev.block(0).diskWrite(sb);

    debugLog("popFreeBlock -> ", freeAddr);
    return freeAddr;
}

void makeINodeBlock(D)(D dev) {
    auto blkAddr = dev.popFreeBlock();
    auto sb = dev.block(0).diskRead!Superblock();

    INodeBlock inodeBlk;
    foreach(i, ref inode; inodeBlk.inodes[0 .. $-2]) {
	inode.nextFree.blk = blkAddr;
	inode.nextFree.index = i + 1;
    }

    inodeBlk.inodes[$-1].nextFree = sb.freeINode;
    sb.freeINode.blk = blkAddr;
    sb.freeINode.index = 0;
    dev.block(blkAddr).diskWrite(inodeBlk);
    dev.block(0).diskWrite(sb);

    debugLog("makeINodeBlock into ", blkAddr);
}

AbsAddr popFreeINode(D)(D dev) {
    auto sb = dev.block(0).diskRead!Superblock();
    if (sb.freeINode.isNull) {
	dev.makeINodeBlock();
	sb = dev.block(0).diskRead!Superblock();
	assert (!sb.freeINode.isNull);
    }

    auto inodeAddr = sb.freeINode;
    INode inode = dev.readINode(inodeAddr);

    sb.freeINode = inode.nextFree;
    dev.block(0).diskWrite(sb);

    debugLog("popFreeINode -> ", inodeAddr);
    return inodeAddr;
}

INode readINode(D)(D dev, AbsAddr inodeAddr) {
    auto blk = dev.block(inodeAddr.blk).diskRead!INodeBlock();
    debugLog("readINode: ", inodeAddr);
    return blk.inodes[inodeAddr.index];
}

void writeINode(D)(D dev, AbsAddr inodeAddr, INode inode) {
    debugLog("writeINode: ", inodeAddr);
    auto blk = dev.block(inodeAddr.blk).diskRead!INodeBlock();
    blk.inodes[inodeAddr.index] = inode;
    dev.block(inodeAddr.blk).diskWrite(blk);
}

void insertBlock(D)(D dev, ref INode inode, uint pos, BlockAddr addr) {
    debugLog("insertBlock: pos=", pos, ", addr=", addr);

    BlockAddr movAddr = addr;

    for (; pos < N_DIRECT && movAddr != NO_BLOCK; pos++)
	swap(movAddr, inode.direct[pos]);

    if (movAddr == NO_BLOCK)
	return;

    immutable nIndirectDataBlks = N_IND_SINGLE * IndexBlock.indices.length;
    for (pos -= N_DIRECT; pos < nIndirectDataBlks && movAddr != NO_BLOCK; pos++) {
	auto index1 = pos / IndexBlock.indices.length;
	auto index2 = pos % IndexBlock.indices.length;

	auto indexBlkAddr = inode.isingle[index1];
	auto indexBlk = dev.block(indexBlkAddr).diskRead!IndexBlock();
	swap(movAddr, indexBlk.indices[index2]);
    }
}

AbsAddr makeDirectory(D)(D dev) {
    AbsAddr inodeAddr = dev.popFreeINode();
    INode inode = dev.readINode(inodeAddr);
    inode.type = INodeType.Directory;

    auto ntAddr = dev.popFreeBlock();
    auto deAddr = dev.popFreeBlock();

    inode.dirHdr.nNameBlocks = 1;
    insertBlock(dev, inode, 0, ntAddr);
    insertBlock(dev, inode, 1, deAddr);
    inode.size = BLOCK_SIZE * 2;

    NameTableBlock ntBlock;  // make an empty Name Table
    dev.block(ntAddr).diskWrite(ntBlock);
    dev.writeINode(inodeAddr, inode);
    return inodeAddr;
}

DEntry readDEntry(D)(D dev, AbsAddr deAddr) {
    auto deBlock = dev.block(deAddr.blk).diskRead!DEntryBlock();
    auto offset = deAddr.index * DENTRY_FRAG_ALIGN;
    auto deHdr = *cast(DEntryHdr*) &deBlock.fragBuf[offset];
    auto nameOffset = offset + DEntryHdr.sizeof;
    char[] name = deBlock.fragBuf[nameOffset .. nameOffset + deHdr.nameLen].to!(char[]);
    return DEntry(deHdr.inodeAddr, name.dup);
}

int findSlot(in BitArray freemap, int numFrags) @trusted {
    int streak = 0;

    for (int pos=0; pos < freemap.length; pos++) {
	if (freemap[pos] == false) {
	    streak++;
	    if (streak == numFrags)
		return pos - numFrags;
	} else {
	    streak = 0;
	}
    }

    return -1;
}

AbsAddr allocDEntry(D)(D dev, in INode inode, int numFrags) {
    const numDEntryBlocks = inode.size.numBlocks - inode.dirHdr.nNameBlocks;
    auto blockAddrs = dataBlocksAddr(&inode, dev);
    foreach (i; 0 .. numDEntryBlocks) {
	auto blkAddr = blockAddrs[inode.dirHdr.nNameBlocks + i];
	auto deBlock = dev.block(blkAddr).diskRead!DEntryBlock();

	// allocate some free space
	auto freemap = BitArray(deBlock.bitmapBuf, DENTRIES_PER_BLOCK);
	int slotIndex = freemap.findSlot(numFrags);
	if (slotIndex == -1)
	    continue;
	assert (slotIndex >= 0);
	assert (slotIndex < DENTRIES_PER_BLOCK);
	return AbsAddr(blkAddr, slotIndex);
    }

    // TODO: Get a free block and make a new space for dentries
    //       out of it
    throw new FSException(FSError.DiskFull);
}


AbsAddr writeDEntry(D)(D dev, ref INode inode, DEntry dentry) {
    auto numFrags = cast(int) (DEntryHdr.sizeof + dentry.name.length).numBlocks(4);
    auto deAddr = dev.allocDEntry(inode, numFrags);
    auto deBlock = dev.block(deAddr.blk).diskRead!DEntryBlock();
    const offset = DENTRY_FRAG_ALIGN * deAddr.index;

    auto hdr = cast(DEntryHdr*) &deBlock.fragBuf[offset];
    hdr.inodeAddr = dentry.inodeAddr;
    hdr.nameLen = cast(ubyte) dentry.name.length;

    auto nameOffset = offset + DEntryHdr.sizeof;
    deBlock.fragBuf[nameOffset .. nameOffset + hdr.nameLen] = cast(ubyte[]) dentry.name;

    debugLog("write dentry `", dentry.name, "` to ", deAddr);
    dev.block(deAddr.blk).diskWrite(deBlock);
    return deAddr;
}

struct NameTable(D) {
    private {
	D dev;
	INode *inode;
    }

    static const ENTRIES_PER_BLOCK = BLOCK_SIZE / NameTableEntry.sizeof;

    this(D dev, ref INode inode) {
	this.dev = dev;
	this.inode = &inode;
    }

    private struct SearchEntry {
	NameTable *parent;
	string name;

	int opApply(int delegate(ref NameTableEntry) dg) {
	    const auto numEntries =
		parent.inode.dirHdr.nNameBlocks * BLOCK_SIZE / AbsAddr.sizeof;
	    assert ((parent.inode.dirHdr.nNameBlocks * BLOCK_SIZE) % AbsAddr.sizeof == 0);

	    size_t h = typeid(string).getHash(&name) % numEntries;
	    auto dataAddrs = dataBlocksAddr(parent.inode, parent.dev);
	    debugLog("inode blocks:");
	    foreach (i; 0 .. parent.inode.size.numBlocks)
		debugLog("#", i, ": ", dataAddrs[i]);

	    auto ntBlock = BlockWriteCache!(D, NameTableBlock)(parent.dev);
	    for (size_t k = h+1; k != h; k = (k+1) % numEntries) {
		auto ntBlkAddr = dataAddrs[k / NameTable.ENTRIES_PER_BLOCK];
		debugLog("SearchEntry: entry #", k,
			 " (block #", (k / NameTable.ENTRIES_PER_BLOCK), ": #", ntBlkAddr, ")");
		ntBlock.set(ntBlkAddr);

		auto tblEntry = &ntBlock.content.entries[k % NameTable.ENTRIES_PER_BLOCK];
		auto tblEntryCur = *tblEntry;
		auto iterRes = dg(*tblEntry);
		if (*tblEntry != tblEntryCur)
		    ntBlock.dirty = true;
		if (iterRes != 0)
		    return iterRes;
	    }

	    return 1;
	}
    }

    void opIndexAssign(AbsAddr inodeAddr, string name) {
	debugLog("NameTable: set `", name, "` to ", inodeAddr);
	foreach (ref tblEntry; SearchEntry(&this, name)) {
	    if (tblEntry.isEmpty || tblEntry.isDeleted) {
		auto dentry = DEntry(inodeAddr, name);
		auto deAddr = dev.writeDEntry(*inode, dentry);
		tblEntry.addr = deAddr;
		assert (tblEntry.isValid);
		return;
	    }
	}

	// No free space in the hash table!
	// TODO: Allocate new blocks and transfer the name table to them.
	// For now, an error will suffice.
	throw new FSException(FSError.DiskFull);
    }

    AbsAddr* opIndex(string name) {
	foreach (ref tblEntry; SearchEntry(&this, name)) {
	    if (tblEntry.isEmpty)
		return null;

	    if (tblEntry.isValid) {
		auto dentry = dev.readDEntry(tblEntry.addr);
		if (dentry.name == name)
		    return &dentry.inodeAddr;
	    }
	}

	return null;
    }

    int opApply(int delegate(DEntry) dg) {
	auto blkAddrs = dataBlocksAddr(inode, dev);
	foreach(i; 0 .. inode.dirHdr.nNameBlocks) {
	    auto ntBlock = dev.block(blkAddrs[i]).diskRead!NameTableBlock();
	    foreach (ntEntry; ntBlock.entries) {
		if (!ntEntry.isValid)
		    continue;
		auto dentry = dev.readDEntry(ntEntry.addr);
		if (dg(dentry))
		    return 0;
	    }
	}
	return 1;
    }
}

void insertDEntry(D)(D dev, AbsAddr dirAddr, string name, AbsAddr fileAddr) {
    auto inode = dev.readINode(dirAddr);
    assert (inode.type == INodeType.Directory);
    auto ntbl = NameTable(dev, &inode);
    ntbl[name] = fileAddr;
}

void mkfs(D)(D dev) {
    Superblock sb;
    sb.magic = MAGIC;
    sb.volumeSize = dev.volumeSize;
    sb.firstFree = 1;
    dev.block(0).diskWrite(sb);

    const auto nblks = sb.volumeSize.numBlocks;
    FreeBlock freeBlk;
    foreach (i; 1 .. nblks - 1) {
	freeBlk.next = i + 1;
	dev.block(i).diskWrite(freeBlk);
    }

    freeBlk.next = NO_BLOCK;
    dev.block(nblks-1).diskWrite(freeBlk);

    auto rootINAddr = dev.makeDirectory();

    sb = dev.block(0).diskRead!Superblock();
    sb.rootINode = rootINAddr;
    dev.block(0).diskWrite(sb);
}


//	Block device implementation: memory-mapped file

class ByteArrayIO {
    private {
	ubyte[] slice;
	size_t offset;
    }

    invariant { assert (offset <= slice.length); }

    this(ubyte[] slice)
    {
	this.slice = slice;
    }

    ubyte[] bytes() { return slice; }

    void write(const(ubyte)[] data)
    {
	slice[offset .. offset+data.length] = data[];
	offset += data.length;
    }

    void write(T)(T n) @trusted if (__traits(isArithmetic, T)) {
	*cast(Unqual!(T)*) &slice[offset] = n;
	offset += T.sizeof;
    }

    ref T read(T)(ref T n) @trusted if (__traits(isArithmetic, T)) {
	n = *cast(Unqual!(T)*) &slice[offset];
	offset += T.sizeof;
	return n;
    }
}

@trusted
struct FileDevice {
    private MmFile mmfile;

    this(string filename, uint sizeBlocks) {
	this.mmfile = new MmFile(filename, MmFile.Mode.readWrite,
				 BLOCK_SIZE * sizeBlocks,
				 null, 0);
    }

    DiskSize volumeSize() { return mmfile.length; }

    ByteArrayIO block(BlockAddr addr) {
	assert (addr < volumeSize.numBlocks);
	debugLog("get block ", addr);
	auto offset = BLOCK_SIZE * addr;
	return new ByteArrayIO(cast(ubyte[]) this.mmfile[offset .. offset+BLOCK_SIZE]);
    }
}


//	Test program
void writeToFile(D, I)(D dev, string name, I input) {
    auto sb = dev.block(0).diskRead!Superblock();
    auto root = dev.readINode(sb.rootINode);

    auto ntbl = NameTable!(D)(dev, root);
    auto inodeAddrPtr = ntbl[name];
    if (inodeAddrPtr is null) {
	auto inodeAddr = dev.popFreeINode();
	inodeAddrPtr = &inodeAddr;
	ntbl[name] = *inodeAddrPtr;
    }
    assert (inodeAddrPtr !is null);

    INode inode = dev.readINode(*inodeAddrPtr);

    ubyte[BLOCK_SIZE] buf;
    uint blkPos = 0;
    while (1) {
	ubyte[] blkData = input.rawRead(buf);
	if (blkData.length == 0)
	    break;

	auto blkAddr = dev.popFreeBlock();
	debugLog("writeToFile: ", blkData.length, " bytes to block ", blkAddr);
	dev.block(blkAddr).write(blkData);
	insertBlock(dev, inode, blkPos, blkAddr);
	inode.size += blkData.length;

	blkPos++;
    }

    dev.writeINode(*inodeAddrPtr, inode);
}

void readFromFile(D, O)(D dev, string name, O output)
{
    auto sb = dev.block(0).diskRead!Superblock();
    INode root = dev.readINode(sb.rootINode);
    auto ntbl = NameTable!(D)(dev, root);

    auto inodeAddrPtr = ntbl[name];
    if (inodeAddrPtr is null)
	throw new FSException(FSError.NoEntry);

    INode inode = dev.readINode(*inodeAddrPtr);
    debugLog("inode = ", inode);

    const auto nblks = inode.size.numBlocks;
    auto nr = 0;
    auto addrs = dataBlocksAddr(&inode, dev);
    foreach (i; 0 .. nblks) {
	auto blkAddr = addrs[i];
	debugLog(" blk #", i, " -> ", blkAddr);
	const auto nbytes = min(BLOCK_SIZE, inode.size - nr);
	output.rawWrite(dev.block(blkAddr).bytes[0 .. nbytes]);
	nr += BLOCK_SIZE;
    }
}

void dumpBlock(D)(D dev, BlockAddr blkAddr) {
    dchar repr(dchar ch) pure nothrow {
	if (ch.isPrintable && !ch.isControl)
	    return ch;
	return '.';
    }

    ubyte[BLOCK_SIZE] blk = dev.block(blkAddr).bytes;
    ulong i = 0;
    while (i < blk.length) {
	auto nb = min(32, blk.length - i);
	auto chars = cast(char[]) blk[i .. i+nb];
	debugLog("    [", chars.map!repr(), "]");
	i += 32;
    }
}

void dumpINode(D)(D dev, AbsAddr inodeAddr)
{
    INode inode = dev.readINode(inodeAddr);
    debugLog("inode = ", inode);
    foreach (blkAddr; inode.direct) {
	if (blkAddr == NO_BLOCK)
	    break;

	debugLog("direct: ", blkAddr);
	dev.dumpBlock(blkAddr);
    }
}

void dumpSuperblock(D)(D dev) {
    dev.block(0).diskRead!Superblock().writeln();
}

void listFiles(D)(D dev) {
    auto sb = dev.block(0).diskRead!Superblock();
    auto inode = dev.readINode(sb.rootINode);
    auto ntbl = NameTable!D(dev, inode);

    writeln("Entries in name table:");
    foreach (dentry; ntbl)
	writefln("%s %s", dentry.inodeAddr, dentry.name);
}

void dumpFreeList(D)(D dev) {
    auto sb = dev.block(0).diskRead!Superblock();
    auto blkAddr = sb.firstFree;
    FreeBlock blk;
    while (blkAddr != 0) {
	blk = dev.block(blkAddr).diskRead!FreeBlock();
	writeln(blkAddr, "\t-> ", blk.next);
	blkAddr = blk.next;
    }
}

void main(string[] args)
{
    if (args.length < 3) {
	writeln("usage: ", args[0], " devfile {mkfs|...}");
	return;
    }

    FileDevice dev = FileDevice(args[1], 4096);

    alias Cmd = void delegate(string[] args);
    immutable Cmd[string] cmds = [
	"mkfs": (args) => mkfs(dev),
	"write": (args) => dev.writeToFile(args[0], stdin),
	"read": (args) =>  dev.readFromFile(args[0], stdout),
	"inode": (args) => dev.dumpINode(AbsAddr(args[0].to!ulong,
						 args[1].to!ulong)),
	"superblock": (args) => dev.dumpSuperblock(),
	"free": (args) => dev.dumpFreeList(),
	"ls": (args) => dev.listFiles(),
    ];

    if (auto cmd = args[2] in cmds) {
	(*cmd)(args[3 .. $]);
    } else {
	stderr.writeln("unrecognized subcommand: ", args[2]);
    }
}
