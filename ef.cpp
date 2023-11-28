/*** 
This file contains the inner functionalities of EF-Index
***/
#include "ef.h"
#include<chrono>
#include<algorithm>
using std::chrono::duration_cast;
using std::chrono::milliseconds;
using std::chrono::nanoseconds;
using std::chrono::system_clock;
using std::chrono::high_resolution_clock;

//Locate the first lineage node to move to
int EF_Index::get_evo_entry(int query_ts, int query_te)
{
	int l = 0, r = length_of_evo_array - 1;
	while (l < r)
	{
		int mid = (l + r) / 2;
		if (evo_array[mid].ts >= query_ts) r = mid;
		else l = mid + 1;
	}
	int evo_entry = l;
	if (evo_array[evo_entry].ts < query_ts || evo_array[evo_entry].te > query_te)
	{
		return -1;
	}
	return evo_entry;
}

//The lookup procedure, which finds the lineage node corresponding to the distinct core
int EF_Index::get_target_lineage_node(int start_node, int query_ts, int query_te)
{
	int current_node = start_node;
	int target_node = -1;
	while (true)
	{
		int picked_nxt_node = -1;
		for (int nxt_node : lineage_graph[current_node].pre_nd)
		{
			if (lineage_graph[nxt_node].ts >= query_ts && lineage_graph[nxt_node].te <= query_te)
			{
				picked_nxt_node = nxt_node;
				break;
			}
		}
		if (picked_nxt_node == -1)
		{
			target_node = current_node;
			break;
		}
		current_node = picked_nxt_node;
	}
	return target_node;
}

//The final function inside EF-Index that handles a TCCS query
void EF_Index::tccs(int query_ts, int query_te, int query_vertex, std::vector<int>& set_of_vertex)
{
	int evo_entry = get_evo_entry(query_ts, query_te);

	if (evo_entry == -1) return;
	int start_node = evo_array[evo_entry].lineage_node;

	auto start_lookup = system_clock::now();

	int target_node = get_target_lineage_node(start_node, query_ts, query_te);

	auto finish_lookup = system_clock::now();
	auto clapse_ns_lk = duration_cast<nanoseconds>(finish_lookup - start_lookup);
	printf("lookup [%d,%d] takes %lld\n", query_ts, query_te, clapse_ns_lk.count());

	int target_elf = lineage_graph[target_node].elf_id;
	elf_list[target_elf].tccs_proc(query_vertex, query_ts, query_te, set_of_vertex);
}

//The real dfs on MTSF
void ELF::dfs_on_forest(int v, int ts, int te, int fa, std::vector<int>& ans)
{
	ans.push_back(v);
	for (int i = elf_head[v]; ~i; i = elf_nxt[i])
	{
		int u = elf_nbr[i];
		if (u == fa) continue;
		if (elf_label[i].first >= ts && elf_label[i].second <= te)
		{
			dfs_on_forest(u, ts, te, v, ans);
		}
	}
}

//The inner interface function that processes a TCCS instance
void ELF::tccs_proc(int query_vertex, int query_ts, int query_te, std::vector<int>& ans)
{
	int forest_vertex = elf_vertex_id(query_vertex);
	if (forest_vertex >= v_raw.size() || v_raw[forest_vertex] != query_vertex)
	{
		return;
	}
	dfs_on_forest(forest_vertex, query_ts, query_te, -1, ans);
	for (int i = 0; i < ans.size(); ++i) ans[i] = v_raw[ans[i]];
}


