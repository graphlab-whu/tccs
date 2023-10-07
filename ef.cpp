#include "ef.h"
#include<chrono>
#include<algorithm>
using std::chrono::duration_cast;
using std::chrono::milliseconds;
using std::chrono::nanoseconds;
using std::chrono::system_clock;
using std::chrono::high_resolution_clock;

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

void EF_Index::tccs(int query_ts, int query_te, int query_vertex, std::vector<int>& set_of_vertex)
{
	int evo_entry = get_evo_entry(query_ts, query_te);//在evo_array上定位到起始时刻不小于查询区间起始时刻的第一个元素

	if (evo_entry == -1) return;//TCCS的结果为空
	int start_node = evo_array[evo_entry].lineage_node;//此TTI对应的lineage node即为在lineage graph上定位目标tkc对应的lineage node的起点

	auto start_lookup = system_clock::now();

	int target_node = get_target_lineage_node(start_node, query_ts, query_te);//在lineage graph的reverse graph上定位目标tkc所对应的lineage node

	auto finish_lookup = system_clock::now();
	auto clapse_ns_lk = duration_cast<nanoseconds>(finish_lookup - start_lookup);
	printf("lookup [%d,%d] takes %lld\n", query_ts, query_te, clapse_ns_lk.count());

	int target_elf = lineage_graph[target_node].elf_id;//获取维护目标tkc连通性的ELF的id
	elf_list[target_elf].tccs_proc(query_vertex, query_ts, query_te, set_of_vertex);//在ELF上获取tccs结果
}

void ELF::dfs_on_forest(int v, int ts, int te, int fa, std::vector<int>& ans)
{
	ans.push_back(v);
	for (int i = elf_head[v]; ~i; i = elf_nxt[i])
	{
		int u = elf_nbr[i];
		if (u == fa) continue;
		if (elf_label[i].first >= ts && elf_label[i].second <= te)//forest边的label在查询区间内，则可继续延申
		{
			dfs_on_forest(u, ts, te, v, ans);
		}
	}
}

void ELF::tccs_proc(int query_vertex, int query_ts, int query_te, std::vector<int>& ans)
{
	int forest_vertex = elf_vertex_id(query_vertex);//将查询点映射为foreset上的连续点编号
	if (forest_vertex >= v_raw.size() || v_raw[forest_vertex] != query_vertex)
	{
		return;
	}
	dfs_on_forest(forest_vertex, query_ts, query_te, -1, ans);//在forest上进行dfs获取结果点集
	for (int i = 0; i < ans.size(); ++i) ans[i] = v_raw[ans[i]];
}


