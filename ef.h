#ifndef EF_H
#define EF_H
#include<vector>

class L_NODE {
public:
	std::vector<int> nxt_nd;
	std::vector<int> pre_nd;
	int elf_id;
	int ts, te;
	int weight;
	int layer_number;
};

class A_NODE {
public:
	int ts, te;
	int lineage_node;
	bool operator<(const A_NODE& another_node) const
	{
		return ts < another_node.ts;
	}
};

class ELF {
public:
	int v_num;
	std::vector<int> v_raw;
	int* elf_head, * elf_nxt, * elf_nbr;
	std::pair<int,int>* elf_label;		
	int idx = 0;

	int elf_vertex_id(int raw_vertex_id)
	{
		return lower_bound(v_raw.begin(), v_raw.end(), raw_vertex_id) - v_raw.begin();
	}
	void init_mem(size_t number_of_vertex)
	{
		elf_head = new int[number_of_vertex];
		elf_nxt = new int[number_of_vertex * 2];
		elf_nbr = new int[number_of_vertex * 2];
		elf_label = new std::pair<int, int>[number_of_vertex * 2];
		memset(elf_head, -1, number_of_vertex * 4);
		idx = 0;
	}
	void insert_edge(int elf_src, int elf_dst, int ts_of_tti, int te_of_tti)
	{
		elf_nbr[idx] = elf_dst, elf_nxt[idx] = elf_head[elf_src], elf_label[idx] = { ts_of_tti, te_of_tti }, elf_head[elf_src] = idx++;
		elf_nbr[idx] = elf_src, elf_nxt[idx] = elf_head[elf_dst], elf_label[idx] = { ts_of_tti, te_of_tti }, elf_head[elf_dst] = idx++;
	}
	void dfs_on_forest(int v, int ts, int te, int fa, std::vector<int>& ans);
	void tccs_proc(int query_vertex, int query_ts, int query_te, std::vector<int>& ans);
};


class EF_Index {
public:
	int _TS, _TE, _K;
	L_NODE* lineage_graph;
	A_NODE* evo_array;
	ELF* elf_list;
	int number_of_lineage_node = -1;
	int length_of_evo_array = -1;
	int entry_node_id = -1;
	int number_of_elf = -1;
	std::vector<std::vector<int>> chain_set;
	EF_Index(){
		_TS = -1, _TE = -1, _K = -1;
		lineage_graph = nullptr;
		evo_array = nullptr;
		elf_list = nullptr;
	}
	EF_Index(int Ts, int Te, int K)
	{
		_TS = Ts, _TE = Te, _K = K;
		lineage_graph = nullptr;
		evo_array = nullptr;
		elf_list = nullptr;
	}
	
	void tccs(int query_ts, int query_te, int query_vertex, std::vector<int>& set_of_vertex);
	int get_evo_entry(int query_ts, int query_te);
	int get_target_lineage_node(int start_node, int query_ts, int query_te);
};


#endif
