/**
  hfsplusclone.c - part of Partclone project
 *
 * Copyright (c) 2007~ Thomas Tsai <thomas at nchc org tw>
 *
 * read hfsplus super block and bitmap
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#include <stdio.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <stdint.h>
#include <malloc.h>
#include <stdarg.h>
#include <getopt.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <linux/types.h>

#include "partclone.h"
#include "hfsplusclone.h"
#include "progress.h"
#include "fs_common.h"

struct HFSPlusVolumeHeader sb;
int ret;

static short reverseShort(short s){
    unsigned char c1, c2;

    c1 = s & 255;
    c2 = (s >> 8) & 255;

    return (c1 << 8)+c2;
}

static int reverseInt(int i){
    unsigned char c1, c2, c3, c4;
    c1 = i & 255;
    c2 = (i >> 8) & 255;
    c3 = (i >> 16)& 255;
    c4 = (i >> 24)& 255;

    return ((int)c1<<24)+((int)c2<<16)+((int)c3<<8)+c4;
}

static int IsAllocationBlockUsed(UInt32 thisAllocationBlock, UInt8* allocationFileContents)
{
    UInt8 thisByte;

    thisByte = allocationFileContents[thisAllocationBlock / 8];
    //log_mesg(0, 0, 0, fs_opt.debug, "IsAB:%i\n", (thisByte & (1 << (7 - (thisAllocationBlock % 8)))));
    return (thisByte & (1 << (7 - (thisAllocationBlock % 8)))) != 0;
}

static void print_fork_data(HFSPlusForkData* fork){
    int i = 0;

    HFSPlusExtentDescriptor* exten;
    log_mesg(2, 0, 0, fs_opt.debug, "%s: logicalSize: %#lx\n", __FILE__, fork->logicalSize);
    log_mesg(2, 0, 0, fs_opt.debug, "%s: clumpSize: %i\n", __FILE__, reverseInt(fork->clumpSize));
    log_mesg(2, 0, 0, fs_opt.debug, "%s: totalBlocks: %i\n", __FILE__, reverseInt(fork->totalBlocks));
    for (i = 0; i < 8; i++ ){
        exten = &fork->extents[i];
        log_mesg(2, 0, 0, fs_opt.debug, "%s: \texten %i startBlock: %i\n", __FILE__, i, reverseInt(exten->startBlock));
        log_mesg(2, 0, 0, fs_opt.debug, "%s: \texten %i blockCount: %i\n", __FILE__, i, reverseInt(fork->extents[i].blockCount));

    }
}

/// open device
static void fs_open(char* device){

    char *buffer;
    short HFS_Version;
    short HFS_Signature;
    int HFS_Clean = 0;

    ret = open(device, O_RDONLY);
    if(lseek(ret, 1024, SEEK_SET) != 1024)
	log_mesg(0, 1, 1, fs_opt.debug, "%s: device %s seek fail\n", __FILE__, device);
	
    buffer = (char*)malloc(sizeof(HFSPlusVolumeHeader));
    if (read (ret, buffer, sizeof(HFSPlusVolumeHeader)) != sizeof(HFSPlusVolumeHeader))
	log_mesg(0, 1, 1, fs_opt.debug, "%s: read HFSPlusVolumeHeader fail\n", __FILE__);
    memcpy(&sb, buffer, sizeof(HFSPlusVolumeHeader));

    HFS_Signature = (short)reverseShort(sb.signature);
    HFS_Version = (short)reverseShort(sb.version);
    HFS_Clean = (reverseInt(sb.attributes)>>8) & 1;


    log_mesg(3, 0, 0, fs_opt.debug, "%s: Signature=%.2s\n", __FILE__, (char*)&HFS_Signature);
    log_mesg(3, 0, 0, fs_opt.debug, "%s: Version=%i\n", __FILE__, HFS_Version);
    log_mesg(3, 0, 0, fs_opt.debug, "%s: Attr-Unmounted=%i(1 is clean, 0 is dirty)\n", __FILE__, HFS_Clean);
    log_mesg(3, 0, 0, fs_opt.debug, "%s: Attr-Inconsistent=%i\n", __FILE__, (reverseInt(sb.attributes)>>11) & 1);

    if(HFS_Signature != HFSPlusSignature && HFS_Signature != HFSXSignature){
        log_mesg(0, 1, 1, fs_opt.debug, "%s: HFS_Plus incorrect signature '%.2s'\n", __FILE__, (char*)&HFS_Signature);
    }

    if(fs_opt.ignore_fschk){
        log_mesg(1, 0, 0, fs_opt.debug, "%s: Ignore filesystem check\n", __FILE__);
    } else {
        if (HFS_Clean)
            log_mesg(3, 0, 0, fs_opt.debug, "%s: HFS_Plus '%s' is clean\n", __FILE__, device);
        else 
            log_mesg(0, 1, 1, fs_opt.debug, "%s: HFS_Plus Volume '%s' is scheduled for a check or it was shutdown\nuncleanly. Please fix it by fsck.\n", __FILE__, device);
    }

    free(buffer);

}

static void fs_close(){

    close(ret);

}

// Device should already be open, bitmap allocated, and progress_bar initialized
// block_offset = how many HFS+ blocks from the start of the device does the HFS+ volume start
static void read_allocation_file(unsigned long* bitmap, progress_bar *prog, UInt32 block_offset) {

    int IsUsed = 0;
    UInt8 *extent_bitmap;
    UInt32 bused = 0, bfree = 0, mused = 0;
    UInt32 block = block_offset, extent_block = 0, tb = 0;
    int allocation_exten = 0;
    UInt32 block_size = 0;
    UInt64 allocation_start_block;
    UInt32 allocation_block_size;
    UInt64 byte_offset = 0;
    UInt32 total_block = reverseInt(sb.totalBlocks);

    tb = reverseInt(sb.totalBlocks);
    block_size = reverseInt(sb.blockSize);
    byte_offset = block_offset * block_size;

    for (allocation_exten = 0; allocation_exten <= 7; allocation_exten++){
        allocation_start_block = block_size*reverseInt(sb.allocationFile.extents[allocation_exten].startBlock);

        allocation_block_size = block_size*reverseInt(sb.allocationFile.extents[allocation_exten].blockCount);
        log_mesg(2, 0, 0, 2, "%s: tb = %lu\n", __FILE__, tb);
        log_mesg(2, 0, 0, 2, "%s: extent_block = %lu\n", __FILE__, extent_block);
        log_mesg(2, 0, 0, 2, "%s: allocation_exten = %i\n", __FILE__, allocation_exten);
        log_mesg(2, 0, 0, 2, "%s: allocation_start_block = %lu\n", __FILE__, allocation_start_block);
        log_mesg(2, 0, 0, 2, "%s: allocation_block_size = %lu\n", __FILE__, allocation_block_size);

        if((allocation_start_block == 0) && (allocation_block_size == 0)){
            continue;
        }

        if(lseek(ret, byte_offset + allocation_start_block, SEEK_SET) != allocation_start_block)
	     log_mesg(0, 1, 1, fs_opt.debug, "%s: start_block %i seek fail\n", __FILE__, allocation_start_block);
        extent_bitmap = (UInt8*)malloc(allocation_block_size);
        if(read(ret, extent_bitmap, allocation_block_size) != allocation_block_size)
	    log_mesg(0, 0, 1, fs_opt.debug, "%s: read hfsp bitmap fail\n", __FILE__);
        for(extent_block = 0 ; (extent_block < allocation_block_size*8) && (block< tb); extent_block++){
            IsUsed = IsAllocationBlockUsed(extent_block, extent_bitmap);
            if (IsUsed){
                bused++;
                pc_set_bit(block_offset + block, bitmap, total_block);
                log_mesg(3, 0, 0, fs_opt.debug, "%s: used block= %i\n", __FILE__, block);
            } else {
                bfree++;
                pc_clear_bit(block_offset + block, bitmap, total_block);
                log_mesg(3, 0, 0, fs_opt.debug, "%s: free block= %i\n", __FILE__, block);
            }
            block++;
            /// update progress
            update_pui(prog, block, block, 0);

        }
        log_mesg(2, 0, 0, 2, "%s: next exten\n", __FILE__);
        log_mesg(2, 0, 0, 2, "%s: extent_bitmap:%i\n", __FILE__, extent_bitmap);
        free(extent_bitmap);
        log_mesg(2, 0, 0, 2, "%s: bfree:%i\n", __FILE__, bfree);
        log_mesg(2, 0, 0, 2, "%s: bused:%i\n", __FILE__, bused);
    }
    mused = (reverseInt(sb.totalBlocks) - reverseInt(sb.freeBlocks));
    if(bused != mused)
        log_mesg(0, 1, 1, fs_opt.debug, "%s: bitmap count error, used:%lu, mbitmap:%lu\n", __FILE__, bused, mused);
}

void read_bitmap(char* device, file_system_info fs_info, unsigned long* bitmap, int pui) {

    int tb = 0;
    int start = 0, bit_size = 1;

    fs_open(device);
    tb = reverseInt(sb.totalBlocks);

    /// init progress
    progress_bar   prog;	/// progress_bar structure defined in progress.h
    progress_init(&prog, start, fs_info.totalblock, fs_info.totalblock, BITMAP, bit_size);

    pc_init_bitmap(bitmap, 0xFF, tb);

    read_allocation_file(bitmap, &prog, 0);

    fs_close();
    /// update progress
    update_pui(&prog, 1, 1, 1);
}

void read_super_blocks(char* device, file_system_info* fs_info)
{

    fs_open(device);
    strncpy(fs_info->fs, hfsplus_MAGIC, FS_MAGIC_SIZE);
    fs_info->block_size  = reverseInt(sb.blockSize);
    fs_info->totalblock  = reverseInt(sb.totalBlocks);
    fs_info->usedblocks  = reverseInt(sb.totalBlocks) - reverseInt(sb.freeBlocks);
    fs_info->device_size = fs_info->block_size * fs_info->totalblock;
    log_mesg(2, 0, 0, 2, "%s: blockSize:%i\n", __FILE__, reverseInt(sb.blockSize));
    log_mesg(2, 0, 0, 2, "%s: totalBlocks:%i\n", __FILE__, reverseInt(sb.totalBlocks));
    log_mesg(2, 0, 0, 2, "%s: freeBlocks:%i\n", __FILE__, reverseInt(sb.freeBlocks));
    print_fork_data(&sb.allocationFile);
    print_fork_data(&sb.extentsFile);
    print_fork_data(&sb.catalogFile);
    print_fork_data(&sb.attributesFile);
    print_fork_data(&sb.startupFile);
    fs_close();
}
