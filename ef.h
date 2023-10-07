#ifndef EF_H
#define EF_H
#include<vector>

class L_NODE {
public:
	std::vector<int> nxt_nd;//节点在Lineage Graph中的邻接节点集合
	std::vector<int> pre_nd;//节点在Reversed Lineage Graph中的邻接节点集合（Evo-Map）
	int elf_id;//节点对应distinct core的连通性在ID为elf_id的ELF中维护
	int ts, te;//节点对应distinct core的TTI为[ts,te],每个lineage node的唯一标识
	int weight;//lineage node的权值，即为对应distinct core中的节点数量
	int layer_number;//lineage node在lineage graph(DAG)中所在的层次,其中entry_node为第0层
};

class A_NODE {
public:
	int ts, te;//数组元素保存的极小TTI为[ts,te]
	int lineage_node;//极小TTI [ts,te]所对应的lineage graph中的节点
	bool operator<(const A_NODE& another_node) const
	{
		return ts < another_node.ts;
	}
};

class ELF {
public:
	int v_num;//ELF包含的点数量
	std::vector<int> v_raw;//ELF的点集在原图中的id所对应的离散化数组，
						   //数组下标+1=原图中点在ELF中的id
	int* elf_head, * elf_nxt, * elf_nbr;//ELF的邻接表（链式前向星实现）
	std::pair<int,int>* elf_label;		//ELF边上的label（TTI）
	int idx = 0;//邻接表末尾位置

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
	int _TS, _TE, _K;//EF_Index存储区间[_TS,_TE]下存在的所有distinct core，k值为_K
	L_NODE* lineage_graph;//[_TS,_TE]下存在的所有distinct core的lineage graph,k值为_K
	A_NODE* evo_array;//Evo-Map中的array
	ELF* elf_list;//所有ELF,保存在一个数组中
	int number_of_lineage_node = -1;//lineage graph中的节点数，等于lineage_graph数组的长度
	int length_of_evo_array = -1;//evo_array的长度
	int entry_node_id = -1;//lineage graph的入口节点，所有节点的公共祖先，有且仅有一个,为[_TS,_TE]导出的TTI
	int number_of_elf = -1;//ELF总数，即为lineage graph分解成的chain总数
	std::vector<std::vector<int>> chain_set;//EF_Index chain_partition得到的chain集合，方便可视化，真实应用场景下不必保存
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
