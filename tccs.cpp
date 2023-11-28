/*** 
This file contains three parts:
Firstly, the implementation of TEL and OTCD.
Secondly, the implementation of OTCD* for zone partition.
Thirdly, the implementation of TCCS, namely functionalities of EF-Index.
For each key function that is newly proposed in the paper, we add a brief introduction.
***/
#define _CRT_SECURE_NO_WARNINGS
#include<malloc.h>
#include<iostream>
#include<fstream>
#include<cstring>
#include<string>
#include<vector>
#include<cstdio>
#include<unordered_map>
#include<unordered_set>
#include<set>
#include<algorithm>
#include<chrono>
#include<array>
#include<map>
#include<queue>
#include"ef.h"
using namespace std;
using std::chrono::duration_cast;
using std::chrono::milliseconds;
using std::chrono::nanoseconds;
using std::chrono::system_clock;
using std::chrono::high_resolution_clock;

void buildtel_fast(int l, int r);
void initMH_fast(int l, int r);
void InitOrderArcSet();
void ArcBetwIntval(int ts, int te, vector<int>& output);


const int VMAX = 4000000; 
const int EMAX = 50000000;
const int TMAX = 50000000;


int vern = 0;
int arcn = 0;
int tmax = 0;
int tmin = 0x7fffffff; 
int span = 0;

struct arc {
	int src, dst, t;
}arcs[EMAX];

int *hs = 0;
int *hd = 0;
int *ht = 0;
int *spre = 0, *snxt = 0;
int *dpre = 0, *dnxt = 0;
int *tpre = 0, *tnxt = 0;
int *telarc = 0;
int idx = 0;

int head = -1, tail = -1;
int *tsarc = 0;
int *tsnxt = 0, *tspre = 0;
int idt = 0;

vector<int> consecutive_timestamp;

int num_of_distinct_ts;

#define _init_arr(name,size) name = new int[size]

void initmem()
{
	_init_arr(hs, VMAX);
	_init_arr(hd, VMAX);
	_init_arr(ht, TMAX);
	_init_arr(spre, EMAX), _init_arr(snxt, EMAX);
	_init_arr(dpre, EMAX), _init_arr(dnxt, EMAX);
	_init_arr(tpre, EMAX), _init_arr(tnxt, EMAX);
	_init_arr(telarc, EMAX);

	_init_arr(tsarc, EMAX);
	_init_arr(tsnxt, EMAX);
	_init_arr(tspre, EMAX);
}

void addt(int t)
{
	if (head == -1) head = idt;
	tsarc[idt] = t;
	tspre[idt] = tail, tsnxt[idt] = -1; 
	if (tail >= 0) tsnxt[tail] = idt; tail = idt;
	idt++;
}

void delt(int t)
{
	int i = (lower_bound(tsarc, tsarc + idt, t) - tsarc);
	if (head == i) head = tsnxt[i];
	else if (tsnxt[i] == -1) tsnxt[tspre[i]] = -1, tail = tspre[i];
	else {
		tsnxt[tspre[i]] = tsnxt[i];
		tspre[tsnxt[i]] = tspre[i];
	}
}

void addarc(int id, int src, int dst, int t)
{
	telarc[idx] = id;
	snxt[idx] = hs[src]; if (hs[src] >= 0) spre[hs[src]] = idx; hs[src] = idx;
	dnxt[idx] = hd[dst]; if (hd[dst] >= 0) dpre[hd[dst]] = idx; hd[dst] = idx;
	tnxt[idx] = ht[t]; if (ht[t] >= 0) tpre[ht[t]] = idx; ht[t] = idx;
	idx++;
}

void delarc_l(int *head, int *next, int* pre, int i, int idx)
{
	if (head[i] == idx) head[i] = next[idx];
	else if (next[idx] == -1) next[pre[idx]] = -1;
	else {
		next[pre[idx]] = next[idx];
		pre[next[idx]] = pre[idx];
	}
}


/*** DataSet Part ***/
const int QMAX = 45000;
struct Q {
	int l, r, k;
}q[QMAX];
int qcnt = 0;

//load the temporal graph, and remap discrete timestamps and vertex numbers to consecutive integers
void loadgraph(const char* name)
{
	ifstream fin(name, ios::in);
#ifdef _DEBUG
	if (fin.is_open() == false) { printf("open graph %s fail\n", name); exit(1); }
#endif
	vector<int> v;

	string l;
	while (getline(fin, l))
	{
		int uvt[3] = { 0 };
		int p = -1, np = -1;
		for (int i = 0; i < 3; ++i)
		{
			p = np + 1, np = l.find(' ', np + 1);
			if (np == -1) np = l.size();
			uvt[i] = stoi(l.substr(p, np - p));
		}
		v.push_back(uvt[0]), v.push_back(uvt[1]);
		tmin = min(tmin, uvt[2]);
		tmax = max(tmax, uvt[2]);
		consecutive_timestamp.push_back(uvt[2]);
		arcs[arcn++] = { uvt[0], uvt[1], uvt[2] };
	}

	span = tmax - tmin;

	
	sort(v.begin(), v.end());
	v.erase(unique(v.begin(), v.end()), v.end());
	vern = v.size();

	
	sort(consecutive_timestamp.begin(), consecutive_timestamp.end());
	consecutive_timestamp.erase(unique(consecutive_timestamp.begin(), consecutive_timestamp.end()), consecutive_timestamp.end());
	num_of_distinct_ts = consecutive_timestamp.size();

	auto get_v = [&](int v_raw) {
		return (lower_bound(v.begin(), v.end(), v_raw) - v.begin()) + 1;
	};

	auto get_t = [&](int t_raw) {
		return (lower_bound(consecutive_timestamp.begin(), consecutive_timestamp.end(), t_raw) - consecutive_timestamp.begin()) + 1;
	};

	for (int i = 0; i < arcn; ++i)
	{
		arcs[i].src = get_v(arcs[i].src), arcs[i].dst = get_v(arcs[i].dst);
		if (arcs[i].src > arcs[i].dst) swap(arcs[i].src, arcs[i].dst);
		arcs[i].t = get_t(arcs[i].t);
	}

	InitOrderArcSet();

}


void loadtest(const char* name)
{
	ifstream fin(name, ios::in);
#ifdef _DEBUG
	if (fin.is_open() == false) { printf("open test %s fail\n", name); exit(1); }
#endif

	string l;
	while (getline(fin, l))
	{
		int lrk[3] = { 0 };
		int p = -1, np = -1;
		for (int i = 0; i < 3; ++i)
		{
			p = np + 1, np = l.find('\t', np + 1);
			if (np == -1) np = l.size();
			lrk[i] = stoi(l.substr(p, np - p));
		}
		q[qcnt++] = { lrk[0], lrk[1], lrk[2] };
	}

}


template<typename T>
void hash_combine(size_t& seed, T const& v)
{
	seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

struct pair_hash
{
	template<typename T1, typename T2>
	size_t operator()(std::pair<T1, T2>const& p) const
	{
		size_t seed = 0;
		hash_combine(seed, p.first);
		hash_combine(seed, p.second);
		return seed;
	}
};

unordered_map<int, int> Mv;
unordered_map<pair<int, int>, int, pair_hash> Mc;
set<pair<int, int>> Hv;

bool cUpd(int src, int dst)
{
#ifdef _DEBUG
	if (Mc.count({ src, dst }) == 0) { printf("cUpd:empty update\n"); exit(1); } 
#endif
	bool ret = false;
	Mc[{src, dst}] --;
	if (Mc[{src, dst}] == 0) { Mc.erase({ src, dst }); ret = true; }
	return ret;
}

void vUpd(int v)
{
#ifdef _DEBUG 
	if (Mv.count(v) == 0) { printf("vUpd:empty update\n"); exit(1); } 
#endif
	int d = Mv[v];
	Hv.erase({ d, v });
	Hv.insert({ d - 1, v });
	Mv[v] --;
}

//The truncation phase of TCD operation
void trunc(int l, int r)
{
	int hh = head, tt = tail;
	while (hh >= 0 && tsarc[hh] < l)
	{
		int t = tsarc[hh];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			if (cUpd(arcs[id].src, arcs[id].dst)) {
				vUpd(arcs[id].src);
				vUpd(arcs[id].dst);
			}
		}
		hh = tsnxt[hh];
	}
	while (tt >= 0 && tsarc[tt] > r)
	{
		int t = tsarc[tt];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			if (cUpd(arcs[id].src, arcs[id].dst)) {
				vUpd(arcs[id].src);
				vUpd(arcs[id].dst);
			}
		}
		tt = tspre[tt];
	}
	head = hh, tail = tt;
}

//The decomposition phase of TCD operation
void decomp(int k)
{
	while (Hv.size() && (Hv.begin()->first<k))
	{
		auto nv = *(Hv.begin());
		Hv.erase(Hv.begin());
		int n = nv.first, v = nv.second;
		Mv.erase(v);
		unordered_set<int> nbr;
		for (int i = hs[v]; ~i; i = snxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			cUpd(arcs[id].src, arcs[id].dst);
			int u = arcs[id].src == v ? arcs[id].dst : arcs[id].src;
			nbr.insert(u);
		}
		for (int i = hd[v]; ~i; i = dnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			cUpd(arcs[id].src, arcs[id].dst);
			int u = arcs[id].src == v ? arcs[id].dst : arcs[id].src;
			nbr.insert(u);
		}
		for (auto u : nbr) vUpd(u);
	}
}

//The TCD Operation
void tcdop(int l, int r, int k)
{
	trunc(l, r);
	decomp(k);
}

int *_hs = 0;
int *_hd = 0;
int *_ht = 0;
int *_spre = 0, *_snxt = 0;
int *_dpre = 0, *_dnxt = 0;
int *_tpre = 0, *_tnxt = 0;
int *_telarc = 0;
int _idx = 0;

int _head = -1, _tail = -1;
int *_tsarc = 0;
int *_tsnxt = 0, *_tspre = 0;
int _idt = 0;

unordered_map<int, int> _Mv;
unordered_map<pair<int, int>, int, pair_hash> _Mc;
set<pair<int, int>> _Hv;

int vbytes = 0; 
int cbytes = 0; 
int tsbytes = 0;
int htbytes = 0;

void _initmem()
{
	_init_arr(_hs, VMAX);
	_init_arr(_hd, VMAX);
	_init_arr(_ht, TMAX);
	_init_arr(_spre, EMAX), _init_arr(_snxt, EMAX);
	_init_arr(_dpre, EMAX), _init_arr(_dnxt, EMAX);
	_init_arr(_tpre, EMAX), _init_arr(_tnxt, EMAX);
	_init_arr(_telarc, EMAX);

	_init_arr(_tsarc, EMAX);
	_init_arr(_tsnxt, EMAX);
	_init_arr(_tspre, EMAX);
}

void bkp()
{
	memcpy(_hs, hs, vbytes);
	memcpy(_hd, hd, vbytes);
	memcpy(_ht, ht, htbytes);
	memcpy(_spre, spre, cbytes); memcpy(_snxt, snxt, cbytes);
	memcpy(_dpre, dpre, cbytes); memcpy(_dnxt, dnxt, cbytes);
	memcpy(_tpre, tpre, cbytes); memcpy(_tnxt, tnxt, cbytes);
	memcpy(_telarc, telarc, cbytes);

	_head = head, _tail = tail;
	memcpy(_tsarc, tsarc, tsbytes);
	memcpy(_tsnxt, tsnxt, tsbytes);
	memcpy(_tspre, tspre, tsbytes);

	_Mv.clear();
	_Mc.clear();
	_Hv.clear();

	_Mv = Mv;
	_Mc = Mc;
	_Hv = Hv;
}

void rst()
{
	memcpy(hs, _hs, vbytes);
	memcpy(hd, _hd, vbytes);
	memcpy(ht, _ht, htbytes);
	memcpy(spre, _spre, cbytes); memcpy(snxt, _snxt, cbytes);
	memcpy(dpre, _dpre, cbytes); memcpy(dnxt, _dnxt, cbytes);
	memcpy(tpre, _tpre, cbytes); memcpy(tnxt, _tnxt, cbytes);
	memcpy(telarc, _telarc, cbytes);

	head = _head, tail = _tail;
	memcpy(tsarc, _tsarc, tsbytes);
	memcpy(tsnxt, _tsnxt, tsbytes);
	memcpy(tspre, _tspre, tsbytes);

	Mv.clear();
	Mc.clear();
	Hv.clear();

	Mv = _Mv;
	Mc = _Mc;
	Hv = _Hv;
}

const int infosum =  12;
enum INFO
{
	CELL,
	SQZ,
	RLC,
	TAG,
	PoR,
	PoU,
	PoL,
	CPoR,
	CPoU,
	CPoL,
	TOTALSIZE,
	SCCNUM,
};
long long cntinfo[infosum] = {0ll};

const int MAX_SPAN = 11000;

void proc(int ts, int te, int ts_i, int te_i);

//The TCD algorithm
void tcd(int ql, int qr, int qk)
{
	int ts = ql;
	while (ts <= qr)
	{
		int te = qr;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		while (te >= ts)
		{
			proc(ts, te, tsarc[head], tsarc[tail]);
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		ts++;
		rst();
	}
}

//The OTCD algorithm
set<pair<int, int>> tti_set;
void otcd(int ql, int qr, int qk)
{
	tti_set.clear();
	unordered_map<int, int> endr; 
	int ts = 0, te = 0;      
	int _ts = ql, _te = qr;	 
	auto rlc = [&](int __te) { 
		if (__te < te)
		{
			cntinfo[INFO::RLC]++;
			te = __te;
		}
	}; 
	auto sqz = [&](int __ts, int __te) {
		if (ts < __ts || te > __te) { 
			cntinfo[INFO::SQZ]++;
			_ts = __ts;  
			_te = __te;  
		}
	};
	auto tag = [&](int __ts)
	{
		if (ts < __ts) 
		{
			cntinfo[INFO::TAG]++;
			for (int r = ts + 1; r <= __ts; ++r)
			{
				if (endr.count(r) == 0)
					endr[r] = -1;
				endr[r] = max(endr[r], te + 1); 
			}

		}
	};
	auto pou = [&](int ts, int te) { return endr.count(ts) && endr[ts] >= te; };

	while (_ts <= _te)
	{
		ts = _ts, te = _te;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		sqz(tsarc[head], tsarc[tail]);
		while (ts <= te)
		{
			proc(ts, te, tsarc[head], tsarc[tail]);
			rlc(tsarc[tail]);
			tag(tsarc[head]);
			if (pou(ts, te)) break;
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		_ts++;
		rst();
	}
}

//Function that initializes a TEL
void buildtel(int l, int r)
{
	memset(hs, -1, VMAX * sizeof(int));
	memset(hd, -1, VMAX * sizeof(int));
	memset(ht, -1, TMAX * sizeof(int));
	head = -1, tail = -1;
	idx = 0, idt = 0;
	vector<int> ts;
	for (int i = 0; i < arcn; ++i)
		if (arcs[i].t >= l && arcs[i].t <= r)
		{
			addarc(i, arcs[i].src, arcs[i].dst, arcs[i].t);
			ts.push_back(arcs[i].t);
		}

	sort(ts.begin(), ts.end());
	ts.erase(unique(ts.begin(), ts.end()), ts.end());
	for (auto t : ts) addt(t);
	
	vbytes = (vern + 1) * sizeof(int);
	cbytes = idx * sizeof(int);
	tsbytes = idt * sizeof(int);
	htbytes = (num_of_distinct_ts + 1) * sizeof(int);
}

bool cAdd(int src, int dst)
{
	if (Mc.count({ src, dst }) == 0)
	{
		Mc[{src, dst}] = 1;
		return true;
	}
	Mc[{src, dst}] ++;
	return false;
}

void vAdd(int v)
{
	if (Mv.count(v) == 0) Mv[v] = 0;
	Hv.erase({ Mv[v], v });
	Mv[v] ++;
	Hv.insert({ Mv[v], v });
}

void initMH(int l, int r)
{
	Mv.clear();
	Mc.clear();
	Hv.clear();
	for (int i = 0; i < arcn; ++i)
	{
		int src = arcs[i].src;
		int dst = arcs[i].dst;
		int t = arcs[i].t;
		if (t < l || t > r) continue;
		if (cAdd(src, dst))
		{
			vAdd(src);
			vAdd(dst);
		}
	}
}


double max_engage = 0.0;
int max_engage_start_t = -1, max_engage_final_t = -1;

unordered_set<pair<int, int>, pair_hash> con_res_set;

double CompEngagementVal_TCD(int ts, int te, int ts_i, int te_i)
{
	vector<int> intval_arcs;
	ArcBetwIntval(ts, te, intval_arcs);
	unordered_set<pair<int, int>, pair_hash> exist_link;
	unordered_map<int, int> nbr_count;
	for (int eid : intval_arcs)
	{
		int src = arcs[eid].src;
		int dst = arcs[eid].dst;
		if (exist_link.count({ src,dst }) == 0)
		{
			if (nbr_count.count(src) == 0) nbr_count[src] = 0;
			nbr_count[src] ++;
			if (nbr_count.count(dst) == 0) nbr_count[dst] = 0;
			nbr_count[dst] ++;
			exist_link.insert({ src,dst });
		}
	}
	double min_egg = 1e9;
	for (auto v2n : Mv)
	{
		int v = v2n.first;
		int in_nbr = v2n.second;
		int tot_nbr = nbr_count[v];
		double eggv = (double)in_nbr / (double)tot_nbr;
		if (eggv < min_egg) {
			min_egg = eggv;
		}
	}
	return min_egg;
}


double size_res = 1e9;
int size_res_start_t = -1;
int size_res_final_t = -1;

double CompSize_TCD(int ts, int te, int ts_i, int te_i)
{
	return (double)Mv.size();
}

void proc(int ts, int te, int ts_i, int te_i)
{
	
	tti_set.insert({ tsarc[head], tsarc[tail] });
	cntinfo[INFO::CELL] ++;
}

enum X_PROPERTY {
	TIME_INSENSITIVE,
	TIME_INCREASING,
	TIME_DECREASING,
};	

enum T_QUERY {
	OPTIMIZING,
	CONSTRAINING,
};

const char* QUERY_TYPE[2] = {
	"OPTIMIZING",
	"CONSTRAINING",
};


typedef std::pair<int, int> TTI;
typedef std::vector<pair<int, int>> LTI;
typedef std::pair<const TTI, LTI> ZONE;
std::unordered_map<TTI, LTI, pair_hash> zone_set;

const int XTYPE_NUM = 10;
enum X_MEANING {
	USER_ENGAGEMENT,
	CONNECTION_STRENTH,
	PERIODICITY,
	PERSISTENCY,
	SIZE,
};

const char* XMEAN_S[XTYPE_NUM] = {
	"USER_ENGAGEMENT",
	"CONNECTION_STRENTH",
	"PERIODICITY",
	"PERSISTENCY",
	"SIZE"
};

typedef double (*xcomputefunc)(int start_time, int end_time, int tti_ts, int tti_te);

std::unordered_map<pair<int, int>, std::unordered_map<int, int>, pair_hash> zone_core_deg;

double CompEngagementVal(int ts, int te, int ts_i, int te_i)
{
	vector<int> intval_arcs;
	ArcBetwIntval(ts, te, intval_arcs);
	unordered_set<pair<int, int>, pair_hash> exist_link;
	unordered_map<int, int> nbr_count;
	for (int eid : intval_arcs)
	{
		int src = arcs[eid].src;
		int dst = arcs[eid].dst;
		if (exist_link.count({ src,dst }) == 0)
		{
			if (nbr_count.count(src) == 0) nbr_count[src] = 0;
			nbr_count[src] ++;
			if (nbr_count.count(dst) == 0) nbr_count[dst] = 0;
			nbr_count[dst] ++;
			exist_link.insert({ src,dst });
		}
	}
	double min_egg = 1e9;
	for (auto v2n : zone_core_deg[{ts_i, te_i}])
	{
		int v = v2n.first;
		int in_nbr = v2n.second;
		int tot_nbr = nbr_count[v];
		double eggv = (double)in_nbr / (double)tot_nbr;
		if (eggv < min_egg) {
			min_egg = eggv;
		}
	}
	return min_egg;
}

double CompConnStrength(int ts, int te, int ts_i, int te_i)
{
	return 0.0;
}

double CompPeriodicity(int ts, int te, int ts_i, int te_i)
{
	return 0.0;
}

double CompPersistency(int ts, int te, int ts_i, int te_i)
{
	return 0.0;
}

double CompSize(int ts, int te, int ts_i, int te_i)
{
	double sz = (double)zone_core_deg[{ts_i, te_i}].size();
	return sz;
}

xcomputefunc XValueComputeFunc[XTYPE_NUM] = {
	CompEngagementVal,
	CompConnStrength,
	CompPeriodicity,
	CompPersistency,
	CompSize,
	NULL,
	NULL,
	NULL,
	NULL,
	NULL,
};

double global_optx = 0.0;	
int qinterval_start = -1, qinterval_end = -1;

void OptLocalSearch(ZONE& z, X_MEANING x, X_PROPERTY xp, int k)
{
	TTI tti = z.first;
	LTI lti = z.second;
	if (xp == X_PROPERTY::TIME_INSENSITIVE || xp == X_PROPERTY::TIME_INCREASING)
	{
		double local_optx = XValueComputeFunc[x](tti.first, tti.second, tti.first, tti.second);
		if (qinterval_start == -1 || local_optx > global_optx)
		{
			global_optx = local_optx;
			qinterval_start = tti.first;
			qinterval_end = tti.second;
		}
	}
	else if (xp == X_PROPERTY::TIME_DECREASING)
	{
		double local_optx = -1.0;
		int l = -1, r = -1;
		for (auto lst : lti)
		{
			double xvalue = XValueComputeFunc[x](lst.first, lst.second, tti.first, tti.second);
			if (xvalue > local_optx)
			{
				local_optx = xvalue;
				l = lst.first, r = lst.second;
			}
		}
		if (local_optx > global_optx)
		{
			global_optx = local_optx;
			qinterval_start = l;
			qinterval_end = r;
		}
	}
}

struct Area {
	int sfrom, sto;
	int efrom, eto;
};
vector<Area> R;

void ConLocalSearch(ZONE& z, X_MEANING x, X_PROPERTY xp, int k, double sigma)
{
	TTI tti = z.first;
	LTI lti = z.second;
	sort(lti.begin(),lti.end());
	size_t n = lti.size();
	
	int* ts = new int[n + 1]; 
	int* te = new int[n + 1]; 
	for (size_t i = 0; i < n; ++i)
	{
		ts[i + 1] = lti[i].first;
		te[i + 1] = lti[i].second;
	}
	int start_t = tti.first;
	int end_t = te[n];
	while (start_t >= ts[1] && end_t >= tti.second)
	{
		
		int* tsi = upper_bound(ts + 1, ts + 1 + n, start_t);
		tsi -= 1;
		int i = tsi - ts;
		if (te[i] < end_t) end_t = te[i];
		double xVal = XValueComputeFunc[x](start_t, end_t, tti.first, tti.second);
		switch (xp) {
			case X_PROPERTY::TIME_DECREASING:
				if (xVal >= sigma)
				{
					R.push_back({ ts[i], end_t, start_t, end_t });
					end_t--;
				}
				else 
				{
					start_t--;
				}
				break;
			case X_PROPERTY::TIME_INCREASING:
				if (xVal >= sigma)
				{
					R.push_back({ start_t,end_t,start_t,tti.second });
					start_t--;
				}
				else
				{
					end_t--;
				}
				break;
		}
	}

	delete[] ts;
	delete[] te;

}

void ZRev(X_MEANING x, X_PROPERTY xp, T_QUERY tq, int k, double sigma)
{
	global_optx = 0.0;
	qinterval_start = -1, qinterval_end = -1;
	R.clear();
	for (ZONE& z : zone_set)
	{
		if (tq == T_QUERY::OPTIMIZING)
		{
			OptLocalSearch(z, x, xp, k);
		}
		else if (tq == T_QUERY::CONSTRAINING)
		{
			ConLocalSearch(z, x, xp, k, sigma);
		}
	}
}

std::map<int, vector<int>> ordered_arc_set;

void InitOrderArcSet()
{
	for (int i = 0; i < arcn; ++i)
	{
		int eId = i;
		int tVal = arcs[i].t;
		ordered_arc_set[tVal].push_back(eId);
	}
}

void ArcBetwIntval(int start_time, int end_time, vector<int>& output)
{
	if (start_time > end_time) return;
	auto start_it = ordered_arc_set.lower_bound(start_time);
	auto end_it = ordered_arc_set.upper_bound(end_time);
	if (end_it == ordered_arc_set.begin()) return;
	end_it--;
	while (start_it != ordered_arc_set.end() && start_it->first <= end_it->first)
	{
		for (int eid : start_it->second)
		{
			output.push_back(eid);
		}
		start_it++;
	}
}

void buildtel_fast(int l, int r)
{
	memset(hs, -1, VMAX * sizeof(int));
	memset(hd, -1, VMAX * sizeof(int));
	memset(ht, -1, TMAX * sizeof(int));
	head = -1, tail = -1;
	idx = 0, idt = 0;
	vector<int> ts;
	vector<int> valid_arcs;
	ArcBetwIntval(l, r, valid_arcs);
	for(auto i:valid_arcs)
	{
		addarc(i, arcs[i].src, arcs[i].dst, arcs[i].t);
		ts.push_back(arcs[i].t);
	}

	sort(ts.begin(), ts.end());
	ts.erase(unique(ts.begin(), ts.end()), ts.end());
	for (auto t : ts) addt(t);
}


void initMH_fast(int l, int r)
{
	Mv.clear();
	Mc.clear();
	Hv.clear();
	vector<int> valid_arcs;
	ArcBetwIntval(l, r, valid_arcs);
	for(int i:valid_arcs)
	{
		int src = arcs[i].src;
		int dst = arcs[i].dst;
		int t = arcs[i].t;
		if (cAdd(src, dst))
		{
			vAdd(src);
			vAdd(dst);
		}
	}
}


const int MAXI = 12000000; 
std::map<int, int> A[MAXI];


void ResetA()
{
	for (int i = 0; i < MAXI; ++i)
		A[i].clear();
	for (int i = 0; i < MAXI; ++i)
	{
		A[i].insert({ 100000000,100000000 });
		A[i].insert({ -1,-1 });
	}
}

void AUpd(int t, int fst_te, int scd_te)
{
	int t_prior = A[t].lower_bound(fst_te)->first;
	int t_follow = (--A[t].lower_bound(fst_te))->first;
	int ins_fst = fst_te, ins_scd = scd_te;
	if (fst_te > A[t][t_prior])
	{
		ins_fst = t_prior;
		A[t].erase(t_prior);
	}
	if (scd_te < t_follow)
	{
		scd_te = A[t][t_follow];
		A[t].erase(t_follow);
	}
	A[t].insert({ins_fst,ins_scd});
}




long long rectangle_prune_count = 0ll;
long long skip_count = 0ll;

void ZPar_ARC(int Ts, int Te, int k)
{
	int ts = Ts, te = Te;
	zone_set.clear();
	rectangle_prune_count = 0ll;
	skip_count = 0ll;
	while (ts <= Te)
	{
		te = Te;
		tcdop(ts, te, k);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		if (A[ts].count(Te + 1))
		{
			skip_count++;
			te = A[ts][Te + 1];
			A[ts].erase(Te + 1);
		}
		while (ts <= te)
		{
			tcdop(ts, te, k);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
			zone_set[{tsarc[head], tsarc[tail]}].push_back({ ts,te }); 
			if (ts < tsarc[head]) rectangle_prune_count++;
			for (int t = ts + 1; t <= tsarc[head]; ++t)
			{
				AUpd(t, te + 1, tsarc[tail] - 1);
			}
			te = tsarc[tail];
			if (A[ts].count(te)) 
			{
				skip_count++;
				te = A[ts][te];
				A[ts].erase(te);
			}
			else te--;
		}
		rst();
		ts++;
	}
}

void get_zone(int ts, int te)
{
	if (zone_set.count({ tsarc[head], tsarc[tail] }) == 0)
	{
		zone_set[{tsarc[head], tsarc[tail]}].push_back({ ts,te });
		return;
	}
	for (auto lti : zone_set[{tsarc[head], tsarc[tail]}])
	{
		if (lti.first <= ts && lti.second >= te)
		{
			return;
		}
	}
	zone_set[{tsarc[head], tsarc[tail]}].push_back({ ts,te });
}

void ZPar_TCD(int ql, int qr, int qk)
{
	zone_set.clear();
	int ts = ql;
	while (ts <= qr)
	{
		int te = qr;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		while (te >= ts)
		{
			get_zone(ts, te);
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		ts++;
		rst();
	}
}


void trie_insert(unordered_map<int,int>& __Mv, int ts, int te);

std::unordered_map<std::pair<int, int>, int, pair_hash> distinct_core_sz;
															 
TTI first_tti;

void ZPar_O(int ql, int qr, int qk)
{
	zone_set.clear();
	zone_core_deg.clear();
	unordered_map<int, int> endr; 
	int ts = 0, te = 0;      
	int _ts = ql, _te = qr;	 
	auto rlc = [&](int __te) {
		if (__te < te)
		{
			cntinfo[INFO::RLC]++;
			te = __te;
		}
	}; 
	auto sqz = [&](int __ts, int __te) {
		if (ts < __ts) { 
			cntinfo[INFO::SQZ]++;
			_ts = __ts;  
		}
	};
	auto tag = [&](int __ts)
	{
		if (ts < __ts) 
		{
			cntinfo[INFO::TAG]++;

			for (int r = ts + 1; r <= __ts; ++r)
			{
				if (endr.count(r) == 0)
					endr[r] = -1;
				endr[r] = max(endr[r], te + 1); 
			}
		}
	};
	auto pou = [&](int ts, int te) { return endr.count(ts) && endr[ts] >= te; };

	while (_ts <= _te)
	{
		ts = _ts, te = _te;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		sqz(tsarc[head], tsarc[tail]);
		while (ts <= te)
		{
			
			distinct_core_sz[{tsarc[head], tsarc[tail]}] = Mv.size();

			
			if (zone_set.size() == 0) first_tti = { tsarc[head], tsarc[tail] };

			
			zone_set[{tsarc[head], tsarc[tail]}].push_back({ts, te});
			rlc(tsarc[tail]);
			tag(tsarc[head]);
			if (pou(ts, te)) break;
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		_ts++;
		rst();
	}
}



void trie_insert(unordered_map<int, int>& __Mv, int ts, int te)
{

}


void ZPrint()
{
	for (auto zone : zone_set)
	{
		auto tti = zone.first;
		auto LTIs = zone.second;
		printf("TTI:[%d,%d]\n", tti.first + tmin, tti.second + tmin);
		printf("LTIs:{\n");
		for (auto lti : LTIs)
		{
			printf("[%d,%d]\n", lti.first + tmin, lti.second + tmin);
		}
		printf("}\n");
	}
	printf("\n");
}


typedef void (*clapsefunc)(int Ts, int Te, int k);
void PClapse(int Ts, int Te, int k, clapsefunc func, const char* graph_name)
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	func(Ts, Te, k);
	auto t_final = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t_final - t_start);
	printf("([%d, %d], %d, %s, %s) on %s:%lldns\n", Ts, Te, k, XMEAN_S[X_MEANING::USER_ENGAGEMENT], QUERY_TYPE[T_QUERY::OPTIMIZING], graph_name, clapse_ns.count());
}

void PClapse_ZPar_O(int Ts, int Te, int k, const char* graph_name)
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	ZPar_O(Ts, Te, k);
	auto t_final = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t_final - t_start);
	printf("ZPar_O ([%d, %d], %d, %s, %s) on %s:%lldns, zone_set size:%llu\n", Ts, Te, k, XMEAN_S[X_MEANING::USER_ENGAGEMENT], 
			QUERY_TYPE[T_QUERY::OPTIMIZING], graph_name, clapse_ns.count(), zone_set.size());
}

void PClapse_TXCQ_2Phase(int Ts, int Te, int k, const char* graph_name)
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	ZPar_O(Ts, Te, k);
	auto t_final1 = system_clock::now();
	ZRev(X_MEANING::USER_ENGAGEMENT, X_PROPERTY::TIME_INCREASING, T_QUERY::OPTIMIZING, k, 0.6);
	auto t_final2 = system_clock::now();
	auto clapse_ns_ph1 = duration_cast<nanoseconds>(t_final1 - t_start);
	auto clapse_ns_tot = duration_cast<nanoseconds>(t_final2 - t_start);
	printf("TxCQ-2Phase ([%d, %d], %d, %s, %s) on %s:Phase1(%lldns),Total(%lldns)\n", Ts, Te, k, XMEAN_S[X_MEANING::USER_ENGAGEMENT], QUERY_TYPE[T_QUERY::OPTIMIZING],
		graph_name, clapse_ns_ph1.count(), clapse_ns_tot.count());
}

void PClapse_TXCQ_Base(int Ts, int Te, int k, const char* graph_name)
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	con_res_set.clear();
	size_res = 1e9;
	size_res_start_t = -1, size_res_final_t = -1;
	auto t_start = system_clock::now();
	tcd(Ts, Te, k);
	auto t_final = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t_final - t_start);
	printf("TxCQ-Base ([%d, %d], %d, %s, %s) on %s:%lldns\n", Ts, Te, k, XMEAN_S[X_MEANING::USER_ENGAGEMENT], QUERY_TYPE[T_QUERY::OPTIMIZING], graph_name, clapse_ns.count());
}

void PClapse_ZPar_TCD(int Ts, int Te, int k, const char* graph_name)
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	ZPar_TCD(Ts, Te, k);
	auto t_final = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t_final - t_start);
	printf("ZPar-TCD ([%d, %d], %d, %s, %s) on %s:%lldns\n", Ts, Te, k, XMEAN_S[X_MEANING::USER_ENGAGEMENT], QUERY_TYPE[T_QUERY::CONSTRAINING], graph_name, clapse_ns.count());
}

void PClapse_OTCD(int Ts, int Te, int k, const char* graph_name)
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	otcd(Ts, Te, k);
	auto t_final = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t_final - t_start);
	vector<int> s;
	printf("OTCD ([%d, %d], %d) on %s:%lldns;TTI Count:%llu\n", Ts, Te, k, graph_name, clapse_ns.count(), tti_set.size());
}

int p[VMAX];
void init_p()
{
	for (int i = 0; i < VMAX; ++i)
	{
		p[i] = i;
	}
}
int find(int v)
{
	if (p[v] != v) p[v] = find(p[v]);
	return p[v];
}
void combine(int u, int v)
{
	int pu = find(u);
	int pv = find(v);
	if (pu != pv) p[pu] = pv;
}
bool in_same_set(int u, int v)
{
	return find(u) == find(v);
}

void get_cc(vector<int>& cc, int ts, int te, std::unordered_map<int, int>& __Mv, int user_id)
{
	init_p();
	vector<int> arc_set;
	ArcBetwIntval(ts, te, arc_set);
	for (auto eid : arc_set)
	{
		int u = arcs[eid].src;
		int v = arcs[eid].dst;
		if (__Mv.count(u) > 0 && __Mv.count(v) > 0)
		{
			combine(u, v);
		}
	}
	for (auto p : __Mv)
	{
		int v = p.first;
		if (in_same_set(v, user_id))
		{
			cc.push_back(v);
		}
	}
}

bool in_span(int t, std::pair<int, int> span)
{
	return t >= span.first && t <= span.second;
}

bool double_equal(double a, double b)
{
	return abs(a - b) < 1e-8;
}

void ProcALLCC(int ts, int te, vector<int>& res_ver_set, double& res_engage, int& res_start_t, int& res_end_t)
{
	static int sz[VMAX];
	static double min_engage[VMAX];
	vector<int> arc_set;
	ArcBetwIntval(ts, te, arc_set);
	unordered_set<pair<int, int>, pair_hash> exist_link;
	unordered_map<int, int> nbr_count;
	for (int eid : arc_set)
	{
		int src = arcs[eid].src;
		int dst = arcs[eid].dst;
		if (exist_link.count({ src,dst }) == 0)
		{
			if (nbr_count.count(src) == 0) nbr_count[src] = 0;
			nbr_count[src] ++;
			if (nbr_count.count(dst) == 0) nbr_count[dst] = 0;
			nbr_count[dst] ++;
			exist_link.insert({ src,dst });
		}
	}
	auto __Mv = zone_core_deg[{ts, te}];
	for (auto v2n : __Mv)
	{
		int v = v2n.first;
		int c_nbr = v2n.second;  
		int g_nbr = nbr_count[v];
		double engage = (double)c_nbr / (double)g_nbr;
		p[v] = v;
		min_engage[v] = engage; 
		sz[v] = 1;
	}

	for (int eid : arc_set)
	{
		int u = arcs[eid].src;
		int v = arcs[eid].dst;
		if (__Mv.count(u) == 0 || __Mv.count(v) == 0)
		{
			continue;
		}
		if (!in_same_set(u, v))
		{
			int pu = find(u);
			int pv = find(v);
			sz[pv] += sz[pu];
			min_engage[pv] = min(min_engage[pv], min_engage[pu]);
			p[pu] = pv;
		}
	}

	int opt_engage = 0.0;
	int opt_v = 0;
	int opt_sz = 0;
	for (auto v2n : __Mv)
	{
		int v = v2n.first;
		if (p[v] == v)
		{
			if (min_engage[v] > opt_engage || (double_equal(min_engage[v], opt_engage) && sz[v] < opt_sz))
			{
				opt_v = v;
				opt_engage = min_engage[v];
				opt_sz = sz[v];
			}
		}
	}

	if (opt_engage > res_engage || (double_equal(opt_engage, res_engage) && opt_sz < res_ver_set.size()))
	{
		res_engage = opt_engage;
		res_start_t = ts;
		res_end_t = te;
		res_ver_set.clear();
		for (auto v2n : __Mv)
		{
			int v = v2n.first;
			if (find(v) != opt_v)
			{
				continue;
			}
			res_ver_set.push_back(v);
		}
	}
}
int k_m = 2;

int core_decomposition()
{
	int k = 1;
	while (Hv.size())
	{
		k++;
		decomp(k);
	}
	return k - 1;
}

//The basic function that creates the lineage graph based on retrieved time zones.
void lg_construct(EF_Index* ef)
{
	buildtel(ef->_TS, ef->_TE);
	initMH(ef->_TS, ef->_TE);
	ZPar_O(ef->_TS, ef->_TE, ef->_K);
	size_t number_of_time_zone = zone_set.size();
	ef->lineage_graph = new L_NODE[number_of_time_zone];
	ef->number_of_lineage_node = number_of_time_zone;
	int lineage_node_id = 0;
	std::unordered_map<TTI, int, pair_hash> tti_to_node;
	for (auto time_zone : zone_set)
	{
		TTI tti = time_zone.first;
		ef->lineage_graph[lineage_node_id].ts = tti.first;
		ef->lineage_graph[lineage_node_id].te = tti.second;
		ef->lineage_graph[lineage_node_id].weight = distinct_core_sz[tti];
		tti_to_node[tti] = lineage_node_id;
		lineage_node_id++;
	}
	for (int node_id = 0; node_id < ef->number_of_lineage_node; ++node_id)
	{
		TTI tti = { ef->lineage_graph[node_id].ts, ef->lineage_graph[node_id].te };
		LTI list_of_lti = zone_set[tti];//获取这个node的LTI列表
		int number_of_connection_to_tti = list_of_lti.size() + 1;
																 
		sort(list_of_lti.begin(), list_of_lti.end());
		for (int i = 0; i < number_of_connection_to_tti; ++i)
		{
			int ts = i == number_of_connection_to_tti - 1 ? tti.first : list_of_lti[i].first - 1;
			int te = i == 0 ? tti.second : list_of_lti[i - 1].second + 1;
			if (ts < ef->_TS || te > ef->_TE) continue;
			int prev_node_id = tti_to_node[{ts, te}];
			ef->lineage_graph[node_id].pre_nd.push_back(prev_node_id);
			ef->lineage_graph[prev_node_id].nxt_nd.push_back(node_id);
		}
	}
	ef->entry_node_id = tti_to_node[first_tti];
}

void evo_construct(EF_Index* ef)
{
	int entry_node = ef->entry_node_id;
	int number_of_lineage_node = ef->number_of_lineage_node;
	vector<int> set_of_end_node;
	for (int i = 0; i < number_of_lineage_node; ++i)
	{
		if (ef->lineage_graph[i].nxt_nd.size() == 0)
		{
			set_of_end_node.push_back(i);
		}
	}
	ef->length_of_evo_array = set_of_end_node.size();
	ef->evo_array = new A_NODE[ef->length_of_evo_array];
	for (int i = 0; i < ef->length_of_evo_array; ++i)
	{
		int end_node_id = set_of_end_node[i];
		ef->evo_array[i].ts = ef->lineage_graph[end_node_id].ts;
		ef->evo_array[i].te = ef->lineage_graph[end_node_id].te;
		ef->evo_array[i].lineage_node = end_node_id;
	}
	sort(ef->evo_array, ef->evo_array + ef->length_of_evo_array);
	
}

void compute_layer_number(EF_Index* ef)
{
	int* in_queue = new int[ef->number_of_lineage_node];
	memset(in_queue, 0, 4 * (ef->number_of_lineage_node));
	queue<int> q;
	ef->lineage_graph[ef->entry_node_id].layer_number = 0;
	q.push(ef->entry_node_id);
	in_queue[ef->entry_node_id] = 1;
	while (q.size())//BFS
	{
		int node_id = q.front();
		q.pop();
		for (auto nxt_node_id : ef->lineage_graph[node_id].nxt_nd)

			if (!in_queue[nxt_node_id])
			{
				
				ef->lineage_graph[nxt_node_id].layer_number = ef->lineage_graph[node_id].layer_number + 1;
				
				q.push(nxt_node_id);
				
				in_queue[nxt_node_id] = 1;
			}
	}
	delete[] in_queue;
}

//The initial chain partition function
void chain_partition(EF_Index* ef, vector<vector<int>>& chain_set)
{
	compute_layer_number(ef);
	set<pair<int, int>> heap_of_node_by_layer_number;//<layer number, node id>
	
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ef->lineage_graph[i].layer_number, i});
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//生成一条新的chain
		pair<int, int> top_item_in_heap = *heap_of_node_by_layer_number.begin();
		int first_chain_node = top_item_in_heap.second;
		chain.push_back(first_chain_node);
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());
		int last_chain_node = first_chain_node;
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())
		{
			
			int nxt_chain_node = -1;
			int weight_of_nxt_chain_node = -1;
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].layer_number, nxt_node })
					 &&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node
				   )
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;
											
			chain.push_back(nxt_chain_node);
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
											
			last_chain_node = nxt_chain_node;
		}
		chain_set.push_back(chain);
	}

	
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;
}

void init_tkc_structure(int ts, int te, int k)
{
	buildtel_fast(ts, te);
	initMH_fast(ts, te);
	decomp(k);
}

void trunc_edge_collect(int l, int r, vector<int>& dec_edge)
{
	int hh = head, tt = tail;
	while (hh >= 0 && tsarc[hh] < l)
	{
		int t = tsarc[hh];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			if (cUpd(arcs[id].src, arcs[id].dst)) {
				vUpd(arcs[id].src);
				vUpd(arcs[id].dst);
			}
			dec_edge.push_back(id);
		}
		hh = tsnxt[hh];
	}
	while (tt >= 0 && tsarc[tt] > r)
	{
		int t = tsarc[tt];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			if (cUpd(arcs[id].src, arcs[id].dst)) {
				vUpd(arcs[id].src);
				vUpd(arcs[id].dst);
			}
			dec_edge.push_back(id);
		}
		tt = tspre[tt];
	}
	head = hh, tail = tt;
}

void decomp_edge_collect(int k, vector<int>& dec_edge)
{
	while (Hv.size() && (Hv.begin()->first < k))
	{
		auto nv = *(Hv.begin());
		Hv.erase(Hv.begin());
		int n = nv.first, v = nv.second;
		Mv.erase(v);
		unordered_set<int> nbr;
		for (int i = hs[v]; ~i; i = snxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			cUpd(arcs[id].src, arcs[id].dst);
			int u = arcs[id].src == v ? arcs[id].dst : arcs[id].src;
			nbr.insert(u);
			dec_edge.push_back(id);
		}
		for (int i = hd[v]; ~i; i = dnxt[i])
		{
			int id = telarc[i];
			delarc_l(hs, snxt, spre, arcs[id].src, i);
			delarc_l(hd, dnxt, dpre, arcs[id].dst, i);
			delarc_l(ht, tnxt, tpre, arcs[id].t, i);
			if (ht[arcs[id].t] == -1) delt(arcs[id].t);
			cUpd(arcs[id].src, arcs[id].dst);
			int u = arcs[id].src == v ? arcs[id].dst : arcs[id].src;
			nbr.insert(u);
			dec_edge.push_back(id);
		}
		for (auto u : nbr) vUpd(u);
	}
}

void tcd_edge_collect(int ts, int te, int k, vector<int>& dec_edge)
{
	trunc_edge_collect(ts, te, dec_edge);
	decomp_edge_collect(k, dec_edge);
}

void compute_inc_edge(EF_Index* ef, vector<int>& chain, vector<vector<int>>& inc_edge)
{
	
	for (int i = 0; i < chain.size() - 1; ++i)
	{
		int ts_of_target_tti = ef->lineage_graph[chain[i + 1]].ts;
		int te_of_target_tti = ef->lineage_graph[chain[i + 1]].te;
		vector<int> tcd_dec_edge;
		tcd_edge_collect(ts_of_target_tti, te_of_target_tti, ef->_K, tcd_dec_edge);
		inc_edge.push_back(tcd_dec_edge);
	}
	inc_edge.push_back({});
	
	int x = chain.size() - 1;
	for (int p = head; p != -1; p = tsnxt[p])
	{
		int t = tsarc[p];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			inc_edge[x].push_back(id);
		}
	}

}

//This function construct a specific MTSF, corresponds to MTSF Construction.
void construct_forest(EF_Index* ef, ELF& elf, vector<int>& chain, vector<vector<int>>& inc_edge)
{
	int n = chain.size() - 1;
	for (int i = 0; i < elf.v_num; ++i) p[i] = i;
	for (int i = n; i >= 0; --i)
	{
		for (int eid : inc_edge[i])
		{
			int raw_src = arcs[eid].src;
			int raw_dst = arcs[eid].dst;
			int elf_src = elf.elf_vertex_id(raw_src);
			int elf_dst = elf.elf_vertex_id(raw_dst);
			if (find(elf_src) != find(elf_dst))
			{
				elf.insert_edge(elf_src, elf_dst, ef->lineage_graph[chain[i]].ts, ef->lineage_graph[chain[i]].te);
				combine(elf_src, elf_dst);
			}
		}
	}
}

void create_elf_of_chain(EF_Index* ef, int elf_id, vector<int>& chain)
{
	ELF& elf = ef->elf_list[elf_id];

	init_tkc_structure(ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te, ef->_K);

	size_t number_of_vertex = Mv.size();
	elf.v_num = number_of_vertex;
	for (auto vn : Mv) elf.v_raw.push_back(vn.first);
	sort(elf.v_raw.begin(), elf.v_raw.end());
	elf.init_mem(number_of_vertex);
	vector<vector<int>> inc_edge;
	compute_inc_edge(ef, chain, inc_edge);

	construct_forest(ef, elf, chain, inc_edge);
}

void create_elf(EF_Index* ef, vector<vector<int>>& chain_set)
{
	size_t number_of_elf = chain_set.size();
	ef->elf_list = new ELF[number_of_elf];
	ef->number_of_elf = number_of_elf;
	for (int i = 0; i < number_of_elf; ++i)
	{
		create_elf_of_chain(ef, i, chain_set[i]);
	}
}

void free_elf(EF_Index* ef, int id)
{
	ELF& elf = ef->elf_list[id];
	delete[] elf.elf_head;
	delete[] elf.elf_label;
	delete[] elf.elf_nbr;
	delete[] elf.elf_nxt;
}

void chain_partition_opt(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID);
void elf_construct(EF_Index* ef)
{
	
	static unordered_map<pair<int, int>, int, pair_hash> TTI2ID;
	TTI2ID.clear();
	
	vector<vector<int>> chain_set;
	chain_partition_opt(ef, chain_set, TTI2ID);
	create_elf(ef, chain_set);
}

EF_Index* ef_construct(int Ts, int Te, int K)
{
	EF_Index* ef = new EF_Index(Ts, Te, K);
	lg_construct(ef);
	evo_construct(ef);
	elf_construct(ef);
	return ef;
}

int recover_ts(int t)
{
	if (t > consecutive_timestamp.size() || t < 1)
	{
		printf("timestamp out of range\n");
		return -1;
	}
	t = consecutive_timestamp[t - 1];
	return t;
}

//The following functions dump different properties of an EF-Index
void ef_dump_chain_set(EF_Index* ef)
{
	printf("The EF_Index contains the following chains:\n");
	long long total_cost = 0ll;
	for (int i = 0; i < ef->number_of_elf; ++i)
	{
		auto chain = ef->chain_set[i];
		printf("< %d >", i);
		for (int node_id : chain)
		{
			int ts = recover_ts(ef->lineage_graph[node_id].ts);
			int te = recover_ts(ef->lineage_graph[node_id].te);
			printf("-[%d,%d]", ts, te);
		}
		printf("(Cost:%d)", ef->elf_list[i].v_num);
		total_cost += ef->elf_list[i].v_num;
		printf("\n");
	}
	printf("The total cost of ELF Forests is %lld\n", total_cost);
}

void ef_calc_tot_heap(EF_Index* ef)
{
	unsigned long long tot_mem_of_ef_index = 0ull;
	tot_mem_of_ef_index += (80ull * (unsigned long long)ef->number_of_elf);
	tot_mem_of_ef_index += (88ull * (unsigned long long)ef->number_of_lineage_node);
	for (int i = 0; i < ef->number_of_elf; ++i)
	{
		ELF& elf = ef->elf_list[i];
		tot_mem_of_ef_index += ((unsigned long long)elf.v_num * 4ull);
		tot_mem_of_ef_index += ((unsigned long long)elf.idx * 4ull * 4ull);
		tot_mem_of_ef_index += ((unsigned long long)elf.v_num * 4ull);
	}
	printf("Total heap memory consumed by EF-Index: %llu\n", tot_mem_of_ef_index);
}

void ef_calc_lg_width(EF_Index* ef)
{
	unordered_map<int, int> num_of_nd_per_layer;
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		int layer = ef->lineage_graph[i].layer_number;
		if (num_of_nd_per_layer.count(layer) == 0) num_of_nd_per_layer[layer] = 0;
		num_of_nd_per_layer[layer] ++;
	}
	int max_layer = 0;
	for (auto num_per_layer : num_of_nd_per_layer)
	{
		max_layer = max(max_layer, num_per_layer.second);
	}
	printf("The widest layer in lineage graph contains %d node.\n", max_layer);
}

void ef_dump(EF_Index* ef)
{
	printf("Properties of EF_Index under ([%d,%d],%d)\n", recover_ts(ef->_TS), recover_ts(ef->_TE), ef->_K);
	printf("The number of lineage node is %d\n", ef->number_of_lineage_node);
	printf("The number of ELF instances is %d\n", ef->number_of_elf);
	printf("The number of elements in evo-array is %d\n", ef->length_of_evo_array);

	int tot_lg_edge = 0;

	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		tot_lg_edge += ef->lineage_graph[i].nxt_nd.size();
	}

	printf("The lineage graph contains %d edges\n", tot_lg_edge);

	printf("The evo-array constains the following minimal TTIs:\n");
	for (int i = 0; i < ef->length_of_evo_array; ++i)
	{
		printf("[%d,%d] ", recover_ts(ef->evo_array[i].ts), recover_ts(ef->evo_array[i].te));
	}
	printf("\n");
}

//This is the entry of TCCS query in main
void optimal_tccs(EF_Index* ef, int query_span_ts, int query_span_te, int query_k, int query_vertex, vector<int>& res)
{
	if (ef->_K != query_k)
	{
		printf("The K value of the EF_Index does not match the query k\n");
		return;
	}
	if (ef->_TS > query_span_ts || ef->_TE < query_span_te)
	{
		printf("The Span of the EF_Index does not include the query span\n");
		return;
	}
	ef->tccs(query_span_ts, query_span_te, query_vertex, res);
}

std::unordered_map<int, string> author_name_by_id;//<author-id, author-name>

void read_dblp_author_name(const char* dblp_author_file)
{
	ifstream file_dblp_author_in(dblp_author_file, ios::in);
	string l;
	while (getline(file_dblp_author_in, l))
	{
		int i = l.find(' ', 0);
		string aut_id = l.substr(0, i);
		string aut_name_raw = l.substr(i + 1ll);
		int name_length = aut_name_raw.size() - 2;
		string aut_name = aut_name_raw.substr(1, name_length);
		for (int i = 0; i < aut_name.size(); ++i)
			if (aut_name[i] == '_')
			{
				aut_name[i] = ' ';
			}
		author_name_by_id[stoi(aut_id)] = aut_name;
	}
}


int map_start_time(int ts)
{
	return (lower_bound(consecutive_timestamp.begin(), consecutive_timestamp.end(), ts) - consecutive_timestamp.begin()) + 1;
}

int map_end_time(int te)
{
	return (upper_bound(consecutive_timestamp.begin(), consecutive_timestamp.end(), te) - consecutive_timestamp.begin());
}


int* __hs = 0;
int* __hd = 0;
int* __ht = 0;
int* __spre = 0, * __snxt = 0;
int* __dpre = 0, * __dnxt = 0;
int* __tpre = 0, * __tnxt = 0;
int* __telarc = 0;
int __idx = 0;

int __head = -1, __tail = -1;
int* __tsarc = 0;
int* __tsnxt = 0, * __tspre = 0;
int __idt = 0;

unordered_map<int, int> __Mv;
unordered_map<pair<int, int>, int, pair_hash> __Mc;
set<pair<int, int>> __Hv;

void __initmem()
{
	_init_arr(__hs, VMAX);
	_init_arr(__hd, VMAX);
	_init_arr(__ht, TMAX);
	_init_arr(__spre, EMAX), _init_arr(__snxt, EMAX);
	_init_arr(__dpre, EMAX), _init_arr(__dnxt, EMAX);
	_init_arr(__tpre, EMAX), _init_arr(__tnxt, EMAX);
	_init_arr(__telarc, EMAX);

	_init_arr(__tsarc, EMAX);
	_init_arr(__tsnxt, EMAX);
	_init_arr(__tspre, EMAX);
}

void __bkp()
{
	memcpy(__hs, hs, vbytes);
	memcpy(__hd, hd, vbytes);
	memcpy(__ht, ht, htbytes);
	memcpy(__spre, spre, cbytes); memcpy(__snxt, snxt, cbytes);
	memcpy(__dpre, dpre, cbytes); memcpy(__dnxt, dnxt, cbytes);
	memcpy(__tpre, tpre, cbytes); memcpy(__tnxt, tnxt, cbytes);
	memcpy(__telarc, telarc, cbytes);

	__head = head, __tail = tail;
	memcpy(__tsarc, tsarc, tsbytes);
	memcpy(__tsnxt, tsnxt, tsbytes);
	memcpy(__tspre, tspre, tsbytes);

	__Mv = Mv;
	__Mc = Mc;
	__Hv = Hv;

}

void __rst()
{
	memcpy(hs, __hs, vbytes);
	memcpy(hd, __hd, vbytes);
	memcpy(ht, __ht, htbytes);
	memcpy(spre, __spre, cbytes); memcpy(snxt, __snxt, cbytes);
	memcpy(dpre, __dpre, cbytes); memcpy(dnxt, __dnxt, cbytes);
	memcpy(tpre, __tpre, cbytes); memcpy(tnxt, __tnxt, cbytes);
	memcpy(telarc, __telarc, cbytes);

	head = __head, tail = __tail;
	memcpy(tsarc, __tsarc, tsbytes);
	memcpy(tsnxt, __tsnxt, tsbytes);
	memcpy(tspre, __tspre, tsbytes);

	Mv = __Mv;
	Mc = __Mc;
	Hv = __Hv;
}

struct L_HEAP_ITEM {
	int weight;
	int layer;
	int nid; 
	bool operator<(const L_HEAP_ITEM& another) const
	{
		if (layer != another.layer) return layer < another.layer; 
		return weight > another.weight;
	}
};

void wchain_partition_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	compute_layer_number(ef);
	set<L_HEAP_ITEM> heap_of_node_by_layer_number;//<key, node id>
	
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ ef->lineage_graph[i].weight, ef->lineage_graph[i].layer_number, i });
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;
		L_HEAP_ITEM top_item_in_heap = *heap_of_node_by_layer_number.begin();
		int first_chain_node = top_item_in_heap.nid;
		chain.push_back(first_chain_node);
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());
		int last_chain_node = first_chain_node;
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())
		{
			
			int nxt_chain_node = -1;//记录node id
			int weight_of_nxt_chain_node = -1;//记录weight值
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].weight, ef->lineage_graph[nxt_node].layer_number, nxt_node })
					&&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node
					)
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;
											
			chain.push_back(nxt_chain_node);
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].weight, ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
			//延申的节点从堆中移除
			last_chain_node = nxt_chain_node;
		}
		pair<int, int> TTI = { ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te };
		int ID = chain_set.size();
		TTI2ID[TTI] = ID;
		chain_set.push_back(chain);
	}

	
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;
}

void chain_partition_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	compute_layer_number(ef);
	set<pair<int, int>> heap_of_node_by_layer_number;//<layer number, node id>
	
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ ef->lineage_graph[i].layer_number, i });
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;
		pair<int, int> top_item_in_heap = *heap_of_node_by_layer_number.begin();
		int first_chain_node = top_item_in_heap.second;
		chain.push_back(first_chain_node);
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());
		int last_chain_node = first_chain_node;
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())
		{
			
			int nxt_chain_node = -1;
			int weight_of_nxt_chain_node = -1;
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].layer_number, nxt_node })
					&&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node
					)
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;
			chain.push_back(nxt_chain_node);
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
			//延申的节点从堆中移除
			last_chain_node = nxt_chain_node;
		}
		pair<int, int> TTI = { ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te };
		int ID = chain_set.size();
		TTI2ID[TTI] = ID;
		chain_set.push_back(chain);
	}

	
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;

const int N = 10000010, M = 10000010;
int h[N], e[M], ne[M], idx_bp;
int match[N];
bool st[N];

void add(int a, int b)
{
	e[idx_bp] = b, ne[idx_bp] = h[a], h[a] = idx_bp++;
}

bool find_aug_path(int x)
{
	for (int i = h[x]; i != -1; i = ne[i])
	{
		int j = e[i];
		if (!st[j])
		{
			st[j] = true;
			if (match[j] == -1 || find_aug_path(match[j]))
			{
				match[j] = x;
				return true;
			}
		}
	}

	return false;
}


vector<int> chain_set_dst[N];

//This is the optimal chain partition function
void chain_partition_opt(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	memset(h, -1, sizeof h);
	memset(match, -1, sizeof match);
	memset(st, false, sizeof st);
	idx_bp = 0;
	int max_match = 0;
	int vn = ef->number_of_lineage_node;
	for (int lv = 0; lv < vn; ++lv)
	{
		for (int rv : ef->lineage_graph[lv].nxt_nd)
		{
			add(lv, rv);
		}
	}
	for (int lv = 0; lv < vn; lv++)
	{
		memset(st, false, sizeof st);
		if (find_aug_path(lv)) max_match++;
	}
	
	int cn = vn - max_match;

	init_p();
	for (int v = 0; v < vn; ++v)
	{
		if (match[v] == -1) continue;
		int u = match[v];
		combine(u, v);
	}

	for (int i = 0; i < N; ++i) chain_set_dst[i].clear();
	
	int* in_queue = new int[ef->number_of_lineage_node];
	memset(in_queue, 0, 4 * (ef->number_of_lineage_node));
	queue<int> q;
	q.push(ef->entry_node_id);
	in_queue[ef->entry_node_id] = 1;

	while (q.size())
	{
		int node_id = q.front();
		q.pop();
		int set_id = find(node_id);
		chain_set_dst[set_id].push_back(node_id);
		for (auto nxt_node_id : ef->lineage_graph[node_id].nxt_nd)
		{
			if (!in_queue[nxt_node_id])
			{
				
				q.push(nxt_node_id);
				
				in_queue[nxt_node_id] = 1;
			}
		}
	}
	delete[] in_queue;

	
	for (int i = 0; i < N; ++i)
	{
		if (chain_set_dst[i].size())
		{
			int fst_nd_in_chain = chain_set_dst[i][0];
			int ts = ef->lineage_graph[fst_nd_in_chain].ts;
			int te = ef->lineage_graph[fst_nd_in_chain].te;
			int ID = chain_set.size();
			TTI2ID[{ts, te}] = ID;
			chain_set.push_back(chain_set_dst[i]);
		}
	}

	
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;

}

void create_elf_of_chain_o(EF_Index* ef, int elf_id, vector<int>& chain)
{
	ELF& elf = ef->elf_list[elf_id];

	size_t number_of_vertex = Mv.size();
	elf.v_num = number_of_vertex;
	for (auto vn : Mv) elf.v_raw.push_back(vn.first);
	sort(elf.v_raw.begin(), elf.v_raw.end());
	elf.init_mem(number_of_vertex);
	vector<vector<int>> inc_edge;
	compute_inc_edge(ef, chain, inc_edge);

	construct_forest(ef, elf, chain, inc_edge);

}

//This is the accelerated version of building MTSF for each chain
void create_elf_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID, int ql, int qr, int qk)
{
	size_t number_of_elf = chain_set.size();
	ef->elf_list = new ELF[number_of_elf];
	ef->number_of_elf = number_of_elf;
	
	tti_set.clear();
	unordered_map<int, int> endr; //end_pos for RoU
	int ts = 0, te = 0;      //current cell
	int _ts = ql, _te = qr;	 //first cell in next row
	auto rlc = [&](int __te) {
		if (__te < te)
		{
			cntinfo[INFO::RLC]++;
			te = __te;//PoR
		}
	}; //PoR
	auto sqz = [&](int __ts, int __te) {
		if (ts < __ts || te > __te) { //Overline Trigger
			cntinfo[INFO::SQZ]++;
			
			_ts = __ts;  //PoU
			_te = __te;  //PoL
		}
	};
	auto tag = [&](int __ts)
	{
		if (ts < __ts) //Overline Triggered
		{
			cntinfo[INFO::TAG]++;
			for (int r = ts + 1; r <= __ts; ++r)
			{
				if (endr.count(r) == 0)
					endr[r] = -1;
				endr[r] = max(endr[r], te + 1); //Tag for PoU
			}

		}
	};
	auto pou = [&](int ts, int te) { return endr.count(ts) && endr[ts] >= te; };//PoU

	while (_ts <= _te)
	{
		ts = _ts, te = _te;
		tcdop(ts, te, qk);
		if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		bkp();
		sqz(tsarc[head], tsarc[tail]);
		while (ts <= te)
		{
			
			pair<int, int> TTI = { tsarc[head], tsarc[tail] };
			tti_set.insert(TTI);
			if (TTI2ID.find(TTI) != TTI2ID.end())//当前distinct core为某一chain首,生成chain的MTSF
			{
				int ID = TTI2ID[TTI];
				if (ef->elf_list[ID].idx == 0)
				{
					__bkp();
					create_elf_of_chain_o(ef, ID, chain_set[ID]);
					__rst();
				}
			}

			rlc(tsarc[tail]);
			tag(tsarc[head]);
			if (pou(ts, te)) break;
			te--;
			tcdop(ts, te, qk);
			if (head == -1 || tail == -1 || tsarc[head] > tsarc[tail]) break;
		}
		_ts++;
		rst();
	}
}

void elf_construct_o(EF_Index* ef)
{
	vector<vector<int>> chain_set;
	static unordered_map<pair<int, int>, int, pair_hash> TTI2ID;
	TTI2ID.clear();
	auto t0 = system_clock::now();

	chain_partition_opt(ef, chain_set, TTI2ID);

	auto t1 = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
	printf("lineage-chain-partition takes %lldns\n", clapse_ns.count());

	buildtel(ef->_TS, ef->_TE);
	initMH(ef->_TS, ef->_TE);
	create_elf_o(ef, chain_set, TTI2ID, ef->_TS, ef->_TE, ef->_K);

	auto t2 = system_clock::now();
	clapse_ns = duration_cast<nanoseconds>(t2 - t1);
	printf("MTSFs-Construction takes %lldns\n", clapse_ns.count());

}

EF_Index* ef_construct_o(int Ts, int Te, int K)
{
	EF_Index* ef = new EF_Index(Ts, Te, K);

	auto t0 = system_clock::now();

	lg_construct(ef);

	auto t1 = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
	printf("[%d,%d,%d], lineage-graph-construction takes %lldns\n", Ts, Te, K, clapse_ns.count());

	evo_construct(ef);
	elf_construct_o(ef);
	return ef;
}

vector<int> cc_set[VMAX];
void get_cc_of_tkc(int Ts, int Te, int k, vector<vector<int>>& ccs)
{
	ccs.clear();
	for (int i = 0; i < VMAX; ++i) cc_set[i].clear();//清空cc_set
	//下面三行初始化tkc的TEL
	buildtel(Ts, Te);
	initMH(Ts, Te);
	decomp(k);
	init_p();
	for (auto edge_freq : Mc)
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)
	{
		int v = vertex_deg.first;
		int rv = find(v);
		cc_set[rv].push_back(v);
	}
	for (int i = 0; i < VMAX; ++i)
	{
		if (cc_set[i].size())
		{
			ccs.push_back(cc_set[i]);
		}
	}
}

void print_tccs_ef_clapse_per_cc(EF_Index* ef, int _ts, int _te, int _k)
{
	vector<vector<int>> ccs;
	get_cc_of_tkc(_ts, _te, _k, ccs);
	long long tot_clapse = 0ll;
	for (int i = 0; i < ccs.size(); ++i)
	{
		vector<int> ans;
		auto t0 = system_clock::now();
		optimal_tccs(ef, _ts, _te, _k, ccs[i][0], ans);
		auto t1 = system_clock::now();
		auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
		tot_clapse += clapse_ns.count();
		printf("TKC(%d, %d, %d), TCCS-EF on CC-%d takes:%lld\n", _ts, _te, _k, i, tot_clapse);
	}
}

void tccs_ol(int _ts, int _te, int _k, int _v, vector<int>& ans)
{
	
	tcdop(_ts, _te, _k);
	init_p();//初始化并查集
	for (auto edge_freq : Mc)
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	int pv = find(_v);
	for (auto vertex_deg : Mv)
	{
		int v = vertex_deg.first;
		if (find(v) == pv) ans.push_back(v);
	}
}

void print_tccs_ol_clapse_per_cc(int Ts, int Te, int _ts, int _te, int _k)
{
	vector<vector<int>> ccs;
	get_cc_of_tkc(_ts, _te, _k, ccs);
	long long tot_clapse = 0ll;
	for (int i = 0; i < ccs.size(); ++i)
	{
		vector<int> ans;
		buildtel(Ts, Te);
		initMH(Ts, Te);
		auto t0 = system_clock::now();
		tccs_ol(_ts, _te, _k, ccs[i][0], ans);
		if (ans.size() == 1)
		{
			printf("Alert: answer size 1\n");
		}
		auto t1 = system_clock::now();
		auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
		tot_clapse += clapse_ns.count();
		printf("TKC(%d, %d, %d), TCCS-OL on CC-%d takes:%lld\n", _ts, _te, _k, i, tot_clapse);
	}

}

//This function represents the updating method of EF-Index
void ef_expand_forward(EF_Index* ef, int TE)
{
	int _TS = ef->_TS;
	int _TE = ef->_TE;
	int _K = ef->_K;
	if (TE != _TE + 1)
	{
		
		printf("TE != _TE + 1, updating request not supported\n");
		return;
	}
	
	
	buildtel(_TS, TE);
	initMH(_TS, TE);
	decomp(_K);

	if (tsarc[tail] != TE)
	{
		
		ef->_TE = TE;
		return;
	}

	int largest_ts_in_nw_tz = 0;
	vector<L_NODE> nd_of_nw_tz;

	
	int ts = _TS, te = TE;
	
	do {

		L_NODE nw_nd;
		nw_nd.ts = tsarc[head];
		nw_nd.te = tsarc[tail];
		nw_nd.weight = Mv.size();
		nd_of_nw_tz.push_back(nw_nd);

		ts = tsarc[head]; 

		largest_ts_in_nw_tz = ts;

		ts++;
		tcdop(ts, te, _K);
	} while(tail != -1 && head != -1 && tsarc[head] <= tsarc[tail] && tsarc[tail] == TE);
	

	size_t nw_num_of_lineage_node = ef->number_of_lineage_node + nd_of_nw_tz.size();

	L_NODE* nw_lg = new L_NODE[nw_num_of_lineage_node];

	std::unordered_map<TTI, int, pair_hash> tti_to_node;
													

	int i = 0;
	while (i < ef->number_of_lineage_node)
	{
		nw_lg[i].ts = ef->lineage_graph[i].ts;
		nw_lg[i].te = ef->lineage_graph[i].te;
		nw_lg[i].elf_id = ef->lineage_graph[i].elf_id;
		nw_lg[i].weight = ef->lineage_graph[i].weight;
		nw_lg[i].layer_number = ef->lineage_graph[i].layer_number;
		nw_lg[i].nxt_nd = ef->lineage_graph[i].nxt_nd;
		nw_lg[i].pre_nd = ef->lineage_graph[i].pre_nd;
		tti_to_node[{nw_lg[i].ts, nw_lg[i].te}] = i;
		i++;
	}

	int j = 0;
	while(i < nw_num_of_lineage_node)
	{
		nw_lg[i].ts = nd_of_nw_tz[j].ts;
		nw_lg[i].te = nd_of_nw_tz[j].te;
		nw_lg[i].weight = nd_of_nw_tz[j].weight;
		tti_to_node[{nw_lg[i].ts, nw_lg[i].te}] = i;
		i++;
		j++;
	}



	for (int i = 0; i < nd_of_nw_tz.size() - 1; ++i)
	{
		
		int ts_src = nd_of_nw_tz[i].ts;
		int te_src = nd_of_nw_tz[i].te;
		int nd_src = tti_to_node[{ts_src, te_src}];

		
		int ts_dst = nd_of_nw_tz[i + 1].ts;
		int te_dst = nd_of_nw_tz[i + 1].te;
		int nd_dst = tti_to_node[{ts_dst, te_dst}];

		
		nw_lg[nd_src].nxt_nd.push_back(nd_dst);
		nw_lg[nd_dst].pre_nd.push_back(nd_src);
	}


	ts = _TS, te = _TE;
	buildtel(ts, te);
	initMH(ts, te);
	decomp(_K);

	do {
		int TTI_ts = tsarc[head];
		int TTI_te = tsarc[tail];
		
		
		int nd_src = tti_to_node[{TTI_ts, TE}];
		int nd_dst = tti_to_node[{TTI_ts, TTI_te}];

		
		nw_lg[nd_src].nxt_nd.push_back(nd_dst);
		nw_lg[nd_dst].pre_nd.push_back(nd_src);
		ts = TTI_ts;
		ts++;
		tcdop(ts, te, _K);
	} while (tail != -1 && head != -1 && tsarc[head] <= tsarc[tail] && ts <= largest_ts_in_nw_tz);
	

	
	int num_of_nw_tz = nd_of_nw_tz.size();
	int last_nw_nd = tti_to_node[{nd_of_nw_tz[num_of_nw_tz - 1].ts, nd_of_nw_tz[num_of_nw_tz - 1].te}];
	if (nw_lg[last_nw_nd].nxt_nd.size() == 0)
	{
		A_NODE* nw_evo = new A_NODE[ef->length_of_evo_array + 1];
		int i = 0;
		while (i < ef->length_of_evo_array)
		{
			nw_evo[i].ts = ef->evo_array[i].ts;
			nw_evo[i].te = ef->evo_array[i].te;
			nw_evo[i].lineage_node = ef->evo_array[i].lineage_node;
			i++;
		}

		
		nw_evo[i].ts = nd_of_nw_tz[num_of_nw_tz - 1].ts;
		nw_evo[i].te = nd_of_nw_tz[num_of_nw_tz - 1].te;
		nw_evo[i].lineage_node = tti_to_node[{nw_evo[i].ts, nw_evo[i].te}];

		
		delete[] ef->evo_array;
		ef->evo_array = nw_evo;
		ef->length_of_evo_array = ef->length_of_evo_array + 1;//evo_array长度+1
	}

	
	
	delete[] ef->lineage_graph;
	ef->lineage_graph = nw_lg;

	unordered_set<int> chain_head;

	for (auto chain : ef->chain_set)
	{
		chain_head.insert(chain[0]);
	}

	
	if (nw_lg[last_nw_nd].nxt_nd.size() && chain_head.find(nw_lg[last_nw_nd].nxt_nd[0]) != chain_head.end())
	{
		
		int head_id = nw_lg[last_nw_nd].nxt_nd[0];
		int elf_id = nw_lg[head_id].elf_id;

		
		vector<int> nw_chain;//新chain
		for (int i = ef->number_of_lineage_node; i < nw_num_of_lineage_node; ++i)
		{
			nw_chain.push_back(i);
		}
		for (auto nd_id : ef->chain_set[elf_id])
		{
			nw_chain.push_back(nd_id);
		}

		ef->chain_set[elf_id] = nw_chain;

		
		delete[] ef->elf_list[elf_id].elf_head;
		delete[] ef->elf_list[elf_id].elf_nbr;
		delete[] ef->elf_list[elf_id].elf_nxt;
		delete[] ef->elf_list[elf_id].elf_label;
		ef->elf_list[elf_id].idx = 0;
		ef->elf_list[elf_id].v_raw.clear();
		ef->elf_list[elf_id].v_num = 0;

		
		create_elf_of_chain(ef, elf_id, nw_chain);
	}
	else 
	{
		vector<int> nw_chain;
		for (int i = ef->number_of_lineage_node; i < nw_num_of_lineage_node; ++i)
		{
			nw_chain.push_back(i);
		}

		ELF* nw_elf_list = new ELF[ef->number_of_elf + 1];
		for (int i = 0; i < ef->number_of_elf; ++i)
		{
			nw_elf_list[i].elf_head = ef->elf_list[i].elf_head;
			nw_elf_list[i].elf_label = ef->elf_list[i].elf_label;
			nw_elf_list[i].elf_nbr = ef->elf_list[i].elf_nbr;
			nw_elf_list[i].elf_nxt = ef->elf_list[i].elf_nxt;
			nw_elf_list[i].idx = ef->elf_list[i].idx;
			nw_elf_list[i].v_num = ef->elf_list[i].v_num;
			nw_elf_list[i].v_raw = ef->elf_list[i].v_raw;
		}

		
		delete[] ef->elf_list;
		ef->elf_list = nw_elf_list;

		
		create_elf_of_chain(ef, ef->number_of_elf, nw_chain);
		ef->number_of_elf++;
		ef->chain_set.push_back(nw_chain);

	}

	ef->entry_node_id = ef->number_of_lineage_node;
	ef->number_of_lineage_node = nw_num_of_lineage_node;
	ef->_TE = TE;
}

void dfs_label(int v, int fa, ELF& elf, set<pair<int, int>>& cc_label)
{
	for (int i = elf.elf_head[v]; ~i; i = elf.elf_nxt[i])
	{
		int u = elf.elf_nbr[i];
		if (u == fa) continue;
		pair<int, int> label = elf.elf_label[i];
		cc_label.insert(label);
		dfs_label(u, v, elf, cc_label);
	}
}

void dfs_edge(int v, int fa, ELF& elf, vector<pair<pair<int, int>, pair<int, int>>>& cc_edge)
{
	for (int i = elf.elf_head[v]; ~i; i = elf.elf_nxt[i])
	{
		int u = elf.elf_nbr[i];
		if (u == fa) continue;
		pair<int, int> label = elf.elf_label[i];
		cc_edge.push_back({ {v, u},label });
		dfs_edge(u, v, elf, cc_edge);
	}
}

void remap_gnu_e(int gnu, const char* graph_name)//remap by granularity for edge
{
	if (gnu <= 0 || gnu % 3600)
	{
		printf("remap_gnu_e:Invalid gnu value\n");
		return;
	}
	vector<arc> nw_arcs;
	for (int i = 0; i < arcn; ++i)
	{
		int src = arcs[i].src;
		int dst = arcs[i].dst;
		int t = tmin + ( (consecutive_timestamp[arcs[i].t - 1] - tmin) / gnu ) * gnu;
		nw_arcs.push_back({ src, dst, t });
	}

	char gnu_c_str[10];
	string gnu_str;
	if (gnu < 3600 * 24)
	{
		int gnu_h = gnu / 3600;
		sprintf(gnu_c_str, "%d", gnu_h);
		string gnu_num(gnu_c_str);
		gnu_str = gnu_num + "h";
	}
	else//粒度超过1天,文件名前缀为 XXd
	{
		int gnu_d = gnu / 3600 / 24;
		sprintf(gnu_c_str, "%d", gnu_d);
		string gnu_num(gnu_c_str);
		gnu_str = gnu_num + "d";
	}

	string graph_name_str(graph_name);

	string nw_graph_name_str = "./" + gnu_str + "_" + graph_name_str.substr(2);

	ofstream ofile(nw_graph_name_str.c_str());
	if (ofile.is_open() == false)
	{
		printf("Create file: %s failed\n", nw_graph_name_str.c_str());
		return;
	}

	for (auto nw_arc : nw_arcs)
	{
		ofile << nw_arc.src << ' ' << nw_arc.dst << ' ' << nw_arc.t << '\n';
	}
	
	ofile.close();
}

void filter_self_loop(const char* filename)
{
	string nw_file_name(filename);
	nw_file_name += "-without-Selfloop";
	nw_file_name = "./" + nw_file_name;
	ofstream ofile(nw_file_name);
	if (ofile.is_open() == false)
	{
		printf("Unable to create %s file.\n", nw_file_name.c_str());
		exit(1);
	}
	for (int i = 0; i < arcn; ++i)
	{
		if (arcs[i].src != arcs[i].dst)
		{
			ofile << arcs[i].src << ' ' << arcs[i].dst << ' ' << consecutive_timestamp[arcs[i].t - 1] << '\n';
		}
	}
	ofile.close();
}

vector<int> ccv_set[VMAX];
vector<int> cct_set[VMAX];
int cce_cnt[VMAX];
vector<int> cce_set[VMAX];

void init_tcc_prop_set()
{
	for (int i = 0; i < VMAX; ++i)
	{
		ccv_set[i].clear();
		cct_set[i].clear();
		cce_set[i].clear();
		cce_cnt[i] = 0;
	}
}

void compute_tcc_prop_set(ZONE tz, int k)
{
	
	auto TTI = tz.first;
	int TTI_TS = TTI.first, TTI_TE = TTI.second;

	
	buildtel(TTI_TS, TTI_TE);
	initMH(TTI_TS, TTI_TE);
	decomp(k);


	init_p();
	for (auto edge_freq : Mc)
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)
	{
		int v = vertex_deg.first;
		int r = find(v);
		ccv_set[r].push_back(v);
	}
	for (int i = head; ~i; i = tsnxt[i])
	{
		int t = tsarc[i];
		for (int j = ht[t]; ~j; j = tnxt[j])
		{
			int eid = telarc[j];
			int u = arcs[eid].src;
			int v = arcs[eid].dst;
			int ts = arcs[eid].t;
			int r = find(u);
			cct_set[r].push_back(ts);
		}
	}
	for (int i = 0; i < VMAX; ++i)
	{
		if (ccv_set[i].size())
		{
			sort(ccv_set[i].begin(), ccv_set[i].end());
			sort(cct_set[i].begin(), cct_set[i].end());
		}
	}
	for (auto edge_freq : Mc)
	{
		
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		int r = find(u);
		cce_cnt[r] ++;
	}
}

void compute_tcc_prop_set_c(int ts, int te, int k)//获取某个TKC对应TCC的三个Property Set, 输入为TKC参数
{

	buildtel(ts, te);
	initMH(ts, te);
	decomp(k);


	init_p();
	for (auto edge_freq : Mc)
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)
	{
		int v = vertex_deg.first;
		int r = find(v);
		ccv_set[r].push_back(v);
	}
	for (int i = head; ~i; i = tsnxt[i])
	{
		int t = tsarc[i];
		for (int j = ht[t]; ~j; j = tnxt[j])
		{
			int eid = telarc[j];
			int u = arcs[eid].src;
			int v = arcs[eid].dst;
			int ts = arcs[eid].t;
			int r = find(u);
			cct_set[r].push_back(ts);
			cce_set[r].push_back(eid);
		}
	}
	for (int i = 0; i < VMAX; ++i)
	{
		if (ccv_set[i].size())
		{
			sort(ccv_set[i].begin(), ccv_set[i].end());
			sort(cct_set[i].begin(), cct_set[i].end());
		}
	}
	for (auto edge_freq : Mc)
	{
		
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		int r = find(u);
		cce_cnt[r] ++;
	}
}

template<typename T>
struct OPT_TCC_FOUND {
	
	int TTI_TS;
	int TTI_TE;
	int MIN_VERTEX;

	T x_value;
};

void LS_BURST(int k)
{
	OPT_TCC_FOUND<double> opt_tcc_burst = {-1, -1, -1, 0.0};
	for (auto tz : zone_set)
	{
		init_tcc_prop_set();

		compute_tcc_prop_set(tz, k);

		for (int i = 0; i < VMAX; ++i)
		{
			if (ccv_set[i].size())
			{
				
				int TTI_TS = *cct_set[i].begin();
				int TTI_TE = *(--cct_set[i].end());
				int MIN_VERTEX = *ccv_set[i].begin();
				int span_day = (consecutive_timestamp[TTI_TE - 1] - consecutive_timestamp[TTI_TS - 1]) / 86400 + 1;
				double tcc_burstiness = (double)cce_cnt[i] * 2.0 / (double)span_day;
			
				if (opt_tcc_burst.TTI_TS == -1 || opt_tcc_burst.x_value < tcc_burstiness)
				{
					opt_tcc_burst = { TTI_TS, TTI_TE, MIN_VERTEX, tcc_burstiness };
				}

			}
		}
	}

	printf("TCC with maximum burstiness: [%d, %d, %d] \n", opt_tcc_burst.TTI_TS, opt_tcc_burst.TTI_TE, opt_tcc_burst.MIN_VERTEX);
}

struct TCC_SZ {
	int ts, te, vid;
	int val;
	bool operator<(const TCC_SZ& another) const
	{
		return val < another.val;
	}
};

void LS_SIZE(int K, int k)
{
	
	priority_queue<TCC_SZ, vector<TCC_SZ>> heap_for_max_k;
	
	set<pair<pair<int, int>, int>> heap_key;
	for (auto tz : zone_set)
	{
		auto TTI = tz.first;
		int ts = TTI.first, te = TTI.second;
		for (int i = 0; i < VMAX; ++i) ccv_set[i].clear();
		
		buildtel(ts, te);
		initMH(ts, te);
		decomp(k);
		init_p();
		for (auto edge_freq : Mc)
		{
			int u = edge_freq.first.first;
			int v = edge_freq.first.second;
			combine(u, v);
		}
		for (auto vertex_deg : Mv)
		{
			int v = vertex_deg.first;
			int rv = find(v);
			ccv_set[rv].push_back(v);
		}
		for (int i = 0; i < VMAX; ++i)
		{
			if (ccv_set[i].size())
			{
				sort(ccv_set[i].begin(), ccv_set[i].end());
			}
		}
		for (int i = head; ~i; i = tsnxt[i])
		{
			int t = tsarc[i];
			for (int j = ht[t]; ~j; j = tnxt[j])
			{
				int eid = telarc[j];
				int u = arcs[eid].src;
				int v = arcs[eid].dst;
				int ts = arcs[eid].t;
				int r = find(u);
				cct_set[r].push_back(ts);
			}
		}
		for (int i = 0; i < VMAX; ++i)
		{
			if (ccv_set[i].size())
			{
				TCC_SZ tcc_sz = { *cct_set[i].begin(), *(--cct_set[i].end()), *ccv_set[i].begin(), (int)ccv_set[i].size() };
				if (heap_key.find({ {tcc_sz.ts, tcc_sz.te}, tcc_sz.vid }) != heap_key.end())
				{
					continue;
				}
				heap_key.insert({ {tcc_sz.ts, tcc_sz.te}, tcc_sz.vid });
				if (heap_for_max_k.size() < K || (heap_for_max_k.top().val > tcc_sz.val))
				{
					if (heap_for_max_k.size() == K) heap_for_max_k.pop();
					heap_for_max_k.push(tcc_sz);
				}
			}
		}
	}
}

void o_tcc_edge_list(int ts, int te, int k, int v, string file_name)
{
	init_tcc_prop_set();
	compute_tcc_prop_set_c(ts, te, k);
	for (int i = 0; i < VMAX; ++i)
	{
		if (ccv_set[i].size())
		{
			if (ccv_set[i][0] == v)
			{
				ofstream ofile(file_name.c_str());
				ofile << "Source" << "," << "Target" << "," << "Timestamp" << "\n";
				for (int eid : cce_set[i])
				{
					ofile << arcs[eid].src << ',' << arcs[eid].dst << ',' << arcs[eid].t << '\n';
				}
				break;
			}
		}
	}
}

void buildtel_with_given_edge(vector<int> edge_list)
{
	memset(hs, -1, VMAX * sizeof(int));
	memset(hd, -1, VMAX * sizeof(int));
	memset(ht, -1, TMAX * sizeof(int));
	head = -1, tail = -1;
	idx = 0, idt = 0;
	vector<int> ts;
	for(int i : edge_list)
	{
		addarc(i, arcs[i].src, arcs[i].dst, arcs[i].t);
		ts.push_back(arcs[i].t);
	}

	sort(ts.begin(), ts.end());
	ts.erase(unique(ts.begin(), ts.end()), ts.end());
	for (auto t : ts) addt(t);

	vbytes = (vern + 1) * sizeof(int);
	cbytes = idx * sizeof(int);
	tsbytes = idt * sizeof(int);
	htbytes = (num_of_distinct_ts + 1) * sizeof(int);
}

void initMH_with_given_edge(vector<int> edge_list)
{
	Mv.clear();
	Mc.clear();
	Hv.clear();
	for (int i : edge_list)
	{
		int src = arcs[i].src;
		int dst = arcs[i].dst;
		int t = arcs[i].t;
		if (cAdd(src, dst))
		{
			vAdd(src);
			vAdd(dst);
		}
	}
}

void induce_k_h_core(int ts, int te, int k, int h)
{
	unordered_map<pair<int, int>, int, pair_hash> conn_stre;
	for (int i = 0; i < arcn; ++i)
		if (arcs[i].t >= ts && arcs[i].t <= te)
		{
			if (conn_stre.find({ arcs[i].src, arcs[i].dst }) == conn_stre.end())
			{
				conn_stre[{arcs[i].src, arcs[i].dst}] = 0;
			}
			conn_stre[{arcs[i].src, arcs[i].dst}] ++;
		}
	vector<int> edge_list;
	for(int i = 0; i < arcn; ++ i)
		if (arcs[i].t >= ts && arcs[i].t <= te)
			if (conn_stre[{arcs[i].src, arcs[i].dst}] >= h)
			{
				edge_list.push_back(i);
			}
	buildtel_with_given_edge(edge_list);
	initMH_with_given_edge(edge_list);
	decomp(k);
}

int main(int argc, char* argv[])
{
	initmem();
	_initmem();
	__initmem();
	loadgraph(argv[1]);
	loadtest(argv[2]);
	printf("load graph complete\n");

	int Ts = map_start_time(tmin);
	int Te = map_end_time(tmax);

	system("pause");
	return 0;
}
