#ifndef EF_H
#define EF_H
#include<vector>

class L_NODE {
public:
	std::vector<int> nxt_nd;//�ڵ���Lineage Graph�е��ڽӽڵ㼯��
	std::vector<int> pre_nd;//�ڵ���Reversed Lineage Graph�е��ڽӽڵ㼯�ϣ�Evo-Map��
	int elf_id;//�ڵ��Ӧdistinct core����ͨ����IDΪelf_id��ELF��ά��
	int ts, te;//�ڵ��Ӧdistinct core��TTIΪ[ts,te],ÿ��lineage node��Ψһ��ʶ
	int weight;//lineage node��Ȩֵ����Ϊ��Ӧdistinct core�еĽڵ�����
	int layer_number;//lineage node��lineage graph(DAG)�����ڵĲ��,����entry_nodeΪ��0��
};

class A_NODE {
public:
	int ts, te;//����Ԫ�ر���ļ�СTTIΪ[ts,te]
	int lineage_node;//��СTTI [ts,te]����Ӧ��lineage graph�еĽڵ�
	bool operator<(const A_NODE& another_node) const
	{
		return ts < another_node.ts;
	}
};

class ELF {
public:
	int v_num;//ELF�����ĵ�����
	std::vector<int> v_raw;//ELF�ĵ㼯��ԭͼ�е�id����Ӧ����ɢ�����飬
						   //�����±�+1=ԭͼ�е���ELF�е�id
	int* elf_head, * elf_nxt, * elf_nbr;//ELF���ڽӱ���ʽǰ����ʵ�֣�
	std::pair<int,int>* elf_label;		//ELF���ϵ�label��TTI��
	int idx = 0;//�ڽӱ�ĩβλ��

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
	int _TS, _TE, _K;//EF_Index�洢����[_TS,_TE]�´��ڵ�����distinct core��kֵΪ_K
	L_NODE* lineage_graph;//[_TS,_TE]�´��ڵ�����distinct core��lineage graph,kֵΪ_K
	A_NODE* evo_array;//Evo-Map�е�array
	ELF* elf_list;//����ELF,������һ��������
	int number_of_lineage_node = -1;//lineage graph�еĽڵ���������lineage_graph����ĳ���
	int length_of_evo_array = -1;//evo_array�ĳ���
	int entry_node_id = -1;//lineage graph����ڽڵ㣬���нڵ�Ĺ������ȣ����ҽ���һ��,Ϊ[_TS,_TE]������TTI
	int number_of_elf = -1;//ELF��������Ϊlineage graph�ֽ�ɵ�chain����
	std::vector<std::vector<int>> chain_set;//EF_Index chain_partition�õ���chain���ϣ�������ӻ�����ʵӦ�ó����²��ر���
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
