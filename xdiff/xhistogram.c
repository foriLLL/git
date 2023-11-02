/*
 * Copyright (C) 2010, Google Inc.
 * and other copyright owners as documented in JGit's IP log.
 *
 * This program and the accompanying materials are made available
 * under the terms of the Eclipse Distribution License v1.0 which
 * accompanies this distribution, is reproduced below, and is
 * available at http://www.eclipse.org/org/documents/edl-v10.php
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * - Redistributions of source code must retain the above copyright
 *   notice, this list of conditions and the following disclaimer.
 *
 * - Redistributions in binary form must reproduce the above
 *   copyright notice, this list of conditions and the following
 *   disclaimer in the documentation and/or other materials provided
 *   with the distribution.
 *
 * - Neither the name of the Eclipse Foundation, Inc. nor the
 *   names of its contributors may be used to endorse or promote
 *   products derived from this software without specific prior
 *   written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "xinclude.h"

#define MAX_PTR	UINT_MAX
#define MAX_CNT	UINT_MAX

#define LINE_END(n) (line##n + count##n - 1)
#define LINE_END_PTR(n) (*line##n + *count##n - 1)

struct histindex {
	struct record {
		unsigned int ptr, cnt;
		struct record *next;
	} **records, /* an occurrence */
	  **line_map; /* map of line to record chain */
	chastore_t rcha;
	unsigned int *next_ptrs;
	unsigned int table_bits,
		     records_size,
		     line_map_size;

	unsigned int max_chain_length,
		     key_shift,
		     ptr_shift;

	unsigned int cnt,
		     has_common;

	xdfenv_t *env;
	xpparam_t const *xpp;
};

struct region {
	unsigned int begin1, end1;
	unsigned int begin2, end2;
};

#define LINE_MAP(i, a) (i->line_map[(a) - i->ptr_shift])

#define NEXT_PTR(index, ptr) \
	(index->next_ptrs[(ptr) - index->ptr_shift])

#define CNT(index, ptr) \
	((LINE_MAP(index, ptr))->cnt)

#define REC(env, s, l) \
	(env->xdf##s.recs[l - 1])

static int cmp_recs(xrecord_t *r1, xrecord_t *r2)
{
	return r1->ha == r2->ha;

}

#define CMP(i, s1, l1, s2, l2) \
	(cmp_recs(REC(i->env, s1, l1), REC(i->env, s2, l2)))

#define TABLE_HASH(index, side, line) \
	XDL_HASHLONG((REC(index->env, side, line))->ha, index->table_bits)

static int scanA(struct histindex *index, int line1, int count1)
{
	unsigned int ptr, tbl_idx;
	unsigned int chain_len;
	struct record **rec_chain, *rec;

	for (ptr = LINE_END(1); line1 <= ptr; ptr--) {		// line1 + count1 - 1
		tbl_idx = TABLE_HASH(index, 1, ptr);		// 返回一个 index->table_bits 那么长的 hash（也就是在哈希表中的哈希）
		rec_chain = index->records + tbl_idx; // 通过哈希值，找到哈希表中相应的槽位（链表的头）。
		rec = *rec_chain; // 获取此哈希槽中的第一个记录。

		chain_len = 0;
		while (rec) {	// 遍历当前槽位的链表，检查我们是否已经遇到了具有相同哈希值的元素。

			// 如果找到了与当前元素内容相同的记录，我们将其添加到该元素的链表中。(从 1 开始， rec 的 ptr行数 和 现在的 ptr 相同，是同一行)
			if (CMP(index, 1, rec->ptr, 1, ptr)) {
				/*
				 * ptr is identical to another element. Insert
				 * it onto the front of the existing element
				 * chain.
				 */
				NEXT_PTR(index, ptr) = rec->ptr;	// 这两行就是插入了一个节点，第一个相同内容的节点的 cnt 记录出现的次数
				rec->ptr = ptr;
				/* cap rec->cnt at MAX_CNT */		// 所以 rec->cnt 到底记录的是什么？应该是这行内容在这次 file1 中出现的次数
				rec->cnt = XDL_MIN(MAX_CNT, rec->cnt + 1);	// 就是选 rec->cnt + 1 和 最大的无符号整形最大值的  较小者，记录这行出现次数，不超过最大值
				LINE_MAP(index, ptr) = rec;
				goto continue_scan; // 跳转到循环的下一个迭代（ptr--）。
			}

			rec = rec->next; // 移动到链中的下一个记录。
			chain_len++; // 增加链长度计数器。
		}

		if (chain_len == index->max_chain_length)	// 如果当前链的长度已经达到了预设的最大长度，函数将停止并返回错误。
			return -1;

		/*
		 * This is the first time we have ever seen this particular
		 * element in the sequence. Construct a new chain for it.
		 */
		if (!(rec = xdl_cha_alloc(&index->rcha)))
			return -1;
		rec->ptr = ptr;
		rec->cnt = 1;				// 由于这一行第一次出现，所以这一行（rec）的 cnt 是 1
		rec->next = *rec_chain;
		*rec_chain = rec;
		LINE_MAP(index, ptr) = rec;

continue_scan:
		; /* no op */
	}

	return 0;
}

static int try_lcs(struct histindex *index, struct region *lcs, int b_ptr,
	int line1, int count1, int line2, int count2)
{
	unsigned int b_next = b_ptr + 1;
	struct record *rec = index->records[TABLE_HASH(index, 2, b_ptr)];	// 从 histindex 中取出文件 2 的第 i 行对应的链表头节点（头节点肯定存在）
	unsigned int as, ae, bs, be, np, rc;	// a_start, a_end, ...	定义一些变量，用于跟踪匹配区域的开始和结束。
	int should_break;

	for (; rec; rec = rec->next) {
		if (rec->cnt > index->cnt) { // 我已经找到了一个出现次数比较少的匹配 或是 rec 这一行出现了超过 64 次
			if (!index->has_common)		// 对应没找到出现次数少的匹配，rec 这一行出现了超过 64 次，出现太多了我匹配一下和这一行一不一致，命中概率高，命中后
				index->has_common = CMP(index, 1, rec->ptr, 2, b_ptr);
			continue;		// 不论哪种情况，都不匹配了，看下一行
		}

		as = rec->ptr;
		if (!CMP(index, 1, as, 2, b_ptr))		// 两行内容不一致
			continue;

		index->has_common = 1;			// 在这次两个文件的 histogram diff 中已经确定有匹配项，更新
		for (;;) {
			should_break = 0;
			np = NEXT_PTR(index, as);	// np 指向下一个具有相同哈希值的行	    285 行 index.ptr_shift = line1; 因为是递归调用 histogram_diff 方法，每个方法内偏移量直接初始化为 line1
			bs = b_ptr;			// 记录匹配开始位置
			ae = as;	// 终点设置为起点，起止相同，向两侧扩散
			be = bs;
			rc = rec->cnt;		// 可能代表"record count"或类似的意思 似乎是代表这次 diff 中最罕见的匹配块的出现次数？
						// 因为 rec -> cnt 应该代表的是这行内容出现的次数， 初始化为这一行
			while (line1 < as && line2 < bs
				&& CMP(index, 1, as - 1, 2, bs - 1)) {
				as--;		// 向前扩展匹配区域，直到达到文件的起始处或遇到不匹配的行。
				bs--;
				if (1 < rc)	// 如果有多个匹配，选择计数最小的。		意思是选择出现频率最少的块吗
					rc = XDL_MIN(rc, CNT(index, as));		// CNT(index, as) 返回的应该是 index.line_map[as - index.shift]->cnt
			}
			while (ae < LINE_END(1) && be < LINE_END(2)
				&& CMP(index, 1, ae + 1, 2, be + 1)) {
				ae++;
				be++;		// 向后扩展匹配区域，直到达到文件的末尾或遇到不匹配的行。
				if (1 < rc)						// ！我的理解是包含最少出现匹配行的最大匹配块，rc记载这一整连续匹配块里匹配行的出现最小次数
					rc = XDL_MIN(rc, CNT(index, ae));		// 寻找那些可能在各自的文件中只出现一次或出现次数较少的行。这些“独特的”匹配往往更能代表文件之间的真实相似度，因为它们不太可能是由于重复的、常规的文本行而偶然匹配。
			}

			if (b_next <= be)
				b_next = be + 1;	// 已经尝试找到最大连续匹配的行跳过
			if (lcs->end1 - lcs->begin1 < ae - as || rc < index->cnt) {	// 更新 lcs 的位置，要么这个块更大，要么这个块不一定更大，但有一行出现次数更少
				lcs->begin1 = as;					// 块更大的优先级更高		这里我还要具体确认 rc 的作用
				lcs->begin2 = bs;
				lcs->end1 = ae;
				lcs->end2 = be;
				index->cnt = rc;					// 更新这次 diff 中最稀有的行出现次数？所以 index->cnt 只会越来越小
			}

			if (np == 0)				// 这里退出
				break;

			while (np <= ae) {			// 因为 np 指向下一个具有相同哈希值的行
				np = NEXT_PTR(index, np);		// 这个循环检查是否有其他行与当前考察的行 'as' 到 'ae' 之间具有相同的哈希值。
				if (np == 0) {				// 如果有，它将继续沿着链表前进，直到找到一个在 'ae' 之外的行，或链表结束。
					should_break = 1;	// 如果 np 等于0，说明链表到头了，没有更多的相同哈希值的行。
					break;			 // 设置一个标志，表明需要跳出外部循环。
				}
			}

			if (should_break)
				break;

			as = np;				// 将 'as' 更新为链表中的下一个元素，即具有相同哈希值的下一行，然后外部循环将继续处理。这样能保证 b 中这一行不放过 a 中所有相同的位置，找到最优结果
		}
	}
	return b_next;
}

static int fall_back_to_classic_diff(xpparam_t const *xpp, xdfenv_t *env,
		int line1, int count1, int line2, int count2)
{
	xpparam_t xpparam;

	memset(&xpparam, 0, sizeof(xpparam));
	xpparam.flags = xpp->flags & ~XDF_DIFF_ALGORITHM_MASK;

	return xdl_fall_back_diff(env, &xpparam,
				  line1, count1, line2, count2);
}

static inline void free_index(struct histindex *index)
{
	xdl_free(index->records);
	xdl_free(index->line_map);
	xdl_free(index->next_ptrs);
	xdl_cha_free(&index->rcha);
}

static int find_lcs(xpparam_t const *xpp, xdfenv_t *env,
		    struct region *lcs,
		    int line1, int count1, int line2, int count2)
{
	int b_ptr;
	int ret = -1;
	struct histindex index;					// 包含了将要用于查找 LCS 的各种参数和变量，包括哈希表、记录、行映射等等。

	memset(&index, 0, sizeof(index));

	index.env = env;
	index.xpp = xpp;

	index.records = NULL;
	index.line_map = NULL;
	/* in case of early xdl_cha_free() */
	index.rcha.head = NULL;

	index.table_bits = xdl_hashbits(count1);	// 根据行数，确定哈希表的位数 比如只有两行，table_bits 就为 1 个 bit 就够了，大于等于 count1 的第一个 bit数
	index.records_size = 1 << index.table_bits;
	if (!XDL_CALLOC_ARRAY(index.records, index.records_size))
		goto cleanup;

	index.line_map_size = count1;
	if (!XDL_CALLOC_ARRAY(index.line_map, index.line_map_size))
		goto cleanup;

	if (!XDL_CALLOC_ARRAY(index.next_ptrs, index.line_map_size))
		goto cleanup;

	/* lines / 4 + 1 comes from xprepare.c:xdl_prepare_ctx() */
	if (xdl_cha_init(&index.rcha, sizeof(struct record), count1 / 4 + 1) < 0)
		goto cleanup;

	index.ptr_shift = line1;
	index.max_chain_length = 64;		// 这里手工设定一个哈希表对应的链表长度不超过 64，

	if (scanA(&index, line1, count1))	// 只会返回 0 或 -1，0 即代表所有 链表的哈希表 index->records 建立完成，-1 代表错误
		goto cleanup;

	index.cnt = index.max_chain_length + 1;		// 这里我不确定 index.cnt 到底是记录什么

	for (b_ptr = line2; b_ptr <= LINE_END(2); )
		b_ptr = try_lcs(&index, lcs, b_ptr, line1, count1, line2, count2); 	// 赋值给 b_ptr，其实就是 b_ptr++

	if (index.has_common && index.max_chain_length < index.cnt)			// 没有找到相同行，或是找到了匹配行，但是匹配行在 A 中出现超过 64 次
		ret = 1;
	else
		ret = 0;		// 找到相同匹配行

cleanup:
	free_index(&index);
	return ret;
}

static int histogram_diff(xpparam_t const *xpp, xdfenv_t *env,
	int line1, int count1, int line2, int count2)
{
	struct region lcs;
	int lcs_found;
	int result;
redo:
	result = -1;

	if (count1 <= 0 && count2 <= 0)				// 起点都小于等于0 （向前递归的出口）
		return 0;

	if (LINE_END(1) >= MAX_PTR)
		return -1;

	if (!count1) {
		while(count2--)
			env->xdf2.rchg[line2++ - 1] = 1;	// 若一边为空，另一边标记为新增
		return 0;
	} else if (!count2) {
		while(count1--)
			env->xdf1.rchg[line1++ - 1] = 1;
		return 0;
	}

	memset(&lcs, 0, sizeof(lcs));		// 接下来就是两边都不为空，填充 lcs
	lcs_found = find_lcs(xpp, env, &lcs, line1, count1, line2, count2);	// 返回 0 ， // 若返回 1 说明没有找到相同行，或是找到了匹配行，但是匹配行在 A 中出现超过 64 次
	if (lcs_found < 0)
		goto out;
	else if (lcs_found)
		result = fall_back_to_classic_diff(xpp, env, line1, count1, line2, count2);
	else {
		if (lcs.begin1 == 0 && lcs.begin2 == 0) {			// begin 下标从 1 开始，若为 0 即没找到公共子序列，把左右两边 line 全部标记为变化
			while (count1--)
				env->xdf1.rchg[line1++ - 1] = 1;
			while (count2--)
				env->xdf2.rchg[line2++ - 1] = 1;
			result = 0;
		} else {
			result = histogram_diff(xpp, env,
						line1, lcs.begin1 - line1,
						line2, lcs.begin2 - line2);	// 递归上面的部分
			if (result)
				goto out;
			/*
			 * result = histogram_diff(xpp, env,
			 *            lcs.end1 + 1, LINE_END(1) - lcs.end1,
			 *            lcs.end2 + 1, LINE_END(2) - lcs.end2);
			 * but let's optimize tail recursion ourself:			// 手动实现了尾递归优化
			*/
			count1 = LINE_END(1) - lcs.end1;
			line1 = lcs.end1 + 1;
			count2 = LINE_END(2) - lcs.end2;
			line2 = lcs.end2 + 1;
			goto redo;
		}
	}
out:
	return result;
}

int xdl_do_histogram_diff(xpparam_t const *xpp, xdfenv_t *env)
{
	return histogram_diff(xpp, env,
		env->xdf1.dstart + 1, env->xdf1.dend - env->xdf1.dstart + 1,
		env->xdf2.dstart + 1, env->xdf2.dend - env->xdf2.dstart + 1);
}
