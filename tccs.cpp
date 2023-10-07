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

void PClapse_ZPar_O(int Ts, int Te, int k, const char* graph_name)//��TxCQ ([Ts,Te], k)��ִ��ʱ���ӡ���նˣ���λΪ����
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

void PClapse_TXCQ_2Phase(int Ts, int Te, int k, const char* graph_name)//��TxCQ ([Ts,Te], k)��ִ��ʱ���ӡ���նˣ���λΪ����
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	ZPar_O(Ts, Te, k);
	auto t_final1 = system_clock::now();
	ZRev(X_MEANING::USER_ENGAGEMENT, X_PROPERTY::TIME_INCREASING, T_QUERY::OPTIMIZING, k, 0.6);//�������X�ĺ����ʱ��˴���Ҫ�޸Ĳ���
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

void lg_construct(EF_Index* ef)
{
	buildtel(ef->_TS, ef->_TE);
	initMH(ef->_TS, ef->_TE);
	ZPar_O(ef->_TS, ef->_TE, ef->_K);
	size_t number_of_time_zone = zone_set.size();
	ef->lineage_graph = new L_NODE[number_of_time_zone];
	ef->number_of_lineage_node = number_of_time_zone;
	int lineage_node_id = 0;
	std::unordered_map<TTI, int, pair_hash> tti_to_node;//TTI��lineage node id��ӳ��
																		//���ں�������zone adjacency����lineage connection
	for (auto time_zone : zone_set)//��ʼ������time zone��Ӧ��lineage node
	{
		TTI tti = time_zone.first;
		ef->lineage_graph[lineage_node_id].ts = tti.first;//��ʼ��tti��ʼʱ��
		ef->lineage_graph[lineage_node_id].te = tti.second;//��ʼ��tti��ֹʱ��
		ef->lineage_graph[lineage_node_id].weight = distinct_core_sz[tti];//��ʼ��time zone��Ӧdistinct core�ڵ���
		tti_to_node[tti] = lineage_node_id;//����tti��lineage node id��ӳ�䣬���ں�������
		lineage_node_id++;
	}
	for (int node_id = 0; node_id < ef->number_of_lineage_node; ++node_id)//��������lineage node����
	{
		TTI tti = { ef->lineage_graph[node_id].ts, ef->lineage_graph[node_id].te };//��ȡ���node��TTI
		LTI list_of_lti = zone_set[tti];//��ȡ���node��LTI�б�
		int number_of_connection_to_tti = list_of_lti.size() + 1;//��lineage graph�����nodeǰ�ھӽڵ������
																 //=���time zone��lti����+1
		sort(list_of_lti.begin(), list_of_lti.end());//��LTI����ts��С��������
		for (int i = 0; i < number_of_connection_to_tti; ++i)//���λ�ȡ����ڵ�ÿ�������ھӵ�TTI=time zone���ǵ�cell
		{
			int ts = i == number_of_connection_to_tti - 1 ? tti.first : list_of_lti[i].first - 1;
			int te = i == 0 ? tti.second : list_of_lti[i - 1].second + 1;
			if (ts < ef->_TS || te > ef->_TE) continue;//�߽��������һ�������һ��������
			int prev_node_id = tti_to_node[{ts, te}];//������ȷ��[ts,te]��Ϊһ��tti
			ef->lineage_graph[node_id].pre_nd.push_back(prev_node_id);//����node_id->prev_node_id
			ef->lineage_graph[prev_node_id].nxt_nd.push_back(node_id);//����prev_node_id->node_id
		}
	}
	ef->entry_node_id = tti_to_node[first_tti];//����lineage graph����ڽڵ㣬first_tti��ZPar_O�м�¼
}

void evo_construct(EF_Index* ef)
{
	int entry_node = ef->entry_node_id;//��ȡlineage graph��ڽڵ�id
	int number_of_lineage_node = ef->number_of_lineage_node;//��ȡlineage graph��node����
	vector<int> set_of_end_node;//�����ռ�lineage graph�����г���Ϊ��Ľڵ㣨��СTTI�ڵ㣩
	for (int i = 0; i < number_of_lineage_node; ++i)//����lineage graph�����нڵ�����ռ�
	{
		if (ef->lineage_graph[i].nxt_nd.size() == 0)
		{
			set_of_end_node.push_back(i);//�������Ϊ0���ռ�����ڵ��id
		}
	}
	ef->length_of_evo_array = set_of_end_node.size();//����evo_array�ĳ��ȼ�Ϊ����Ϊ���lineage node����
	ef->evo_array = new A_NODE[ef->length_of_evo_array];//��ʼ��evo_array
	for (int i = 0; i < ef->length_of_evo_array; ++i)//����ÿ��evo_array��Ԫ�ص���ʵֵ������TTI��lineage node��id
	{
		int end_node_id = set_of_end_node[i];//��ȡlineage node��id
		ef->evo_array[i].ts = ef->lineage_graph[end_node_id].ts;//����TTI��ʼʱ��
		ef->evo_array[i].te = ef->lineage_graph[end_node_id].te;//����TTI��ֹʱ��
		ef->evo_array[i].lineage_node = end_node_id;//����lineage node �� id
	}
	sort(ef->evo_array, ef->evo_array + ef->length_of_evo_array);//��evo_array������ʼʱ����������
	//����evo_array��Ӧ�Ķ��Ǽ�СTTI�������ʼ��ֹʱ�̶�������ͬ������ֹʱ������ʼʱ�̵���
}

void compute_layer_number(EF_Index* ef)
{
	int* in_queue = new int[ef->number_of_lineage_node];//����һ�����飬��¼ÿ��lineage node�Ƿ�����ӣ��ѱ����㣩
	memset(in_queue, 0, 4 * (ef->number_of_lineage_node));//�������ʼ��Ϊȫ0
	queue<int> q;//����BFS����
	ef->lineage_graph[ef->entry_node_id].layer_number = 0;//��ʼ��entry node�Ĳ���Ϊ��0��
	q.push(ef->entry_node_id);//��entry node���
	in_queue[ef->entry_node_id] = 1;//����entry nodeΪ�Ѿ������
	while (q.size())//BFS
	{
		int node_id = q.front();
		q.pop();
		for (auto nxt_node_id : ef->lineage_graph[node_id].nxt_nd)

			if (!in_queue[nxt_node_id])
			{
				//����layer numberΪ��ǰnode��layer number + 1
				ef->lineage_graph[nxt_node_id].layer_number = ef->lineage_graph[node_id].layer_number + 1;
				//���
				q.push(nxt_node_id);
				//���Ϊ�Ѵ���
				in_queue[nxt_node_id] = 1;
			}
	}
	delete[] in_queue;//�ͷ��ڴ�
}

void chain_partition(EF_Index* ef, vector<vector<int>>& chain_set)
{
	compute_layer_number(ef);
	set<pair<int, int>> heap_of_node_by_layer_number;//<layer number, node id>
	//��setģ��С���ѣ���lineage node�洢������֮���greedy chain generation
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ef->lineage_graph[i].layer_number, i});
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//����һ���µ�chain
		pair<int, int> top_item_in_heap = *heap_of_node_by_layer_number.begin();//�����Ѷ���Ϊchain�ĵ�һ��node
		int first_chain_node = top_item_in_heap.second;//��ȡnode��id
		chain.push_back(first_chain_node);//����һ��node����chain��
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());//�Ƴ��Ѷ�
		int last_chain_node = first_chain_node;//last_chain_node�洢��ǰchain�����һ��node��id����ʼ��Ϊfirst_chain_node
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())//����greedy approach��������chain
		{
			//�������������last_chain_node���ڵ�node���ҵ�weight��С����һ��
			int nxt_chain_node = -1;//��¼node id
			int weight_of_nxt_chain_node = -1;//��¼weightֵ
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].layer_number, nxt_node })//nxt_node���ڶ����δ������
					 &&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node//nxt_node��weight����
				   )
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;//���û���ҵ���˵���Ѿ�û�к��node������node��������ĳһchain
											//��ǰchain�������
			chain.push_back(nxt_chain_node);//��ǰchain����һ���ڵ�
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
											//����Ľڵ�Ӷ����Ƴ�
			last_chain_node = nxt_chain_node;//������ĩβ�ڵ�Ϊ������Ľڵ㣬��������
		}
		chain_set.push_back(chain);//�ռ������ɵ�chain
	}

	//����chain���ɺ�����ÿ��lineage node��chain���,��elf_id
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;//Ŀǰ��ʵ������EF_Index���ر���ÿ��chain��ʲô�����ڱ���ֻ��Ϊ�˿��ӻ�
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
	//��ʱtkc��structure��Mv,Hv,Mc,TEL��Ӧ���Ѿ���Ӧchain�е�һ��distinct core
	for (int i = 0; i < chain.size() - 1; ++i)
	{
		int ts_of_target_tti = ef->lineage_graph[chain[i + 1]].ts;
		int te_of_target_tti = ef->lineage_graph[chain[i + 1]].te;
		vector<int> tcd_dec_edge;//�ռ�tcd�����м��ٵ�ʱ���
		tcd_edge_collect(ts_of_target_tti, te_of_target_tti, ef->_K, tcd_dec_edge);
		inc_edge.push_back(tcd_dec_edge);//chain�е�i��distinct core����i + 1��distinct core���ٵ�ʱ���
	}
	inc_edge.push_back({});//�������һ���߼�(��ʼΪ��),���ڱ���chain�����һ��distinct core��ʱ���
	//chain�����һ��distinct core������ʱ��߼�Ϊ�������ߣ�ȫ������
	int x = chain.size() - 1;//���һ��distinct core���ڵ��±�
	for (int p = head; p != -1; p = tsnxt[p])//�ռ�TEL��ʣ�µ�����ʱ��ߣ��ȱ���TL���ٱ���ÿ��TL[t]���ϵ�ʱ���
	{
		int t = tsarc[p];
		for (int i = ht[t]; ~i; i = tnxt[i])
		{
			int id = telarc[i];
			inc_edge[x].push_back(id);
		}
	}

}

void construct_forest(EF_Index* ef, ELF& elf, vector<int>& chain, vector<vector<int>>& inc_edge)
{
	int n = chain.size() - 1;
	for (int i = 0; i < elf.v_num; ++i) p[i] = i;//��ʼ�����鼯������forest����(ELF forest����:0-(v_num-1))
	for (int i = n; i >= 0; --i)
	{
		for (int eid : inc_edge[i])
		{
			int raw_src = arcs[eid].src;
			int raw_dst = arcs[eid].dst;
			int elf_src = elf.elf_vertex_id(raw_src);
			int elf_dst = elf.elf_vertex_id(raw_dst);
			if (find(elf_src) != find(elf_dst))//�����������ELF forest�л�����ͨ������forest�����������
			{
				elf.insert_edge(elf_src, elf_dst, ef->lineage_graph[chain[i]].ts, ef->lineage_graph[chain[i]].te);
				combine(elf_src, elf_dst);//ά�����鼯�������˵���ͨ
			}
		}
	}
}

void create_elf_of_chain(EF_Index* ef, int elf_id, vector<int>& chain)
{
	ELF& elf = ef->elf_list[elf_id];

	init_tkc_structure(ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te, ef->_K);

	size_t number_of_vertex = Mv.size();
	elf.v_num = number_of_vertex;//����elf�Ľڵ�������Ϊchain�е�һ��node��Ӧtkc�Ľڵ���
	for (auto vn : Mv) elf.v_raw.push_back(vn.first);//����elf�Ľڵ㼯���ڵ���Ϊԭʱ��ͼ�еı�ţ����ܲ�������
	sort(elf.v_raw.begin(), elf.v_raw.end());//elf�ڵ㼯������������ӳ�䵽elf��forest�ڵĽڵ��ţ�������
	elf.init_mem(number_of_vertex);//��ʼ��elf foreset���ڽӱ��ڴ�
	vector<vector<int>> inc_edge;//chain����������distinct core֮��������߼�,����֮�󹹽�forest
	compute_inc_edge(ef, chain, inc_edge);//��ȡchain����distinct core��������

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
	//��elf_construct����TTI2IDֻ��Ϊ�˼���chain_partition_opt������,������õ���create_elf����create_elf_o,���û��ʵ������
	static unordered_map<pair<int, int>, int, pair_hash> TTI2ID;//����������distinct core��TTI������ŵ�ӳ�䣬����chain_partition_o�м���
	TTI2ID.clear();//ÿ�ι����µ�ELF֮ǰ��������׵���ID��ӳ�伯
	
	vector<vector<int>> chain_set;
	chain_partition_opt(ef, chain_set, TTI2ID);
	create_elf(ef, chain_set);
}

EF_Index* ef_construct(int Ts, int Te, int K)
{
	EF_Index* ef = new EF_Index(Ts, Te, K);//��ʼ��EF_Index,Ϊ���صĶ���
	lg_construct(ef);
	evo_construct(ef);
	elf_construct(ef);
	return ef;
}

int recover_ts(int t)//��������ʱ�����ԭΪԭͼ����ɢ��ʱ���,t���������������ʱ�����Χ��
{
	if (t > consecutive_timestamp.size() || t < 1)
	{
		printf("timestamp out of range\n");
		return -1;
	}
	t = consecutive_timestamp[t - 1];
	return t;
}

void ef_dump_chain_set(EF_Index* ef)//��ӡEF_Index������chain,TTIΪԭͼʱ��,�����㿪��
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

void ef_calc_tot_heap(EF_Index* ef)//����EF_Index������ܶ��ڴ�
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

void ef_calc_lg_width(EF_Index* ef)//����EF_Index��lineage graph��������Ľڵ���
{
	unordered_map<int, int> num_of_nd_per_layer;//ͳ��lineage graphÿ��ڵ���
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

void ef_dump(EF_Index* ef)//��ӡһ��EF_Index�������Ϣ
{
	printf("Properties of EF_Index under ([%d,%d],%d)\n", recover_ts(ef->_TS), recover_ts(ef->_TE), ef->_K);
	printf("The number of lineage node is %d\n", ef->number_of_lineage_node);
	printf("The number of ELF instances is %d\n", ef->number_of_elf);
	printf("The number of elements in evo-array is %d\n", ef->length_of_evo_array);

	int tot_lg_edge = 0;//ͳ��lineage relation����������Ϊlineage graph���ܱ���

	for (int i = 0; i < ef->number_of_lineage_node; ++i)//����lineage graph�����нڵ㣬�ۼӸ����ڵ�ĳ�����Ŀ
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


void optimal_tccs(EF_Index* ef, int query_span_ts, int query_span_te, int query_k, int query_vertex, vector<int>& res)
{
	if (ef->_K != query_k)//��ѯ��k��EF_Index��ƥ��
	{
		printf("The K value of the EF_Index does not match the query k\n");
		return;
	}
	if (ef->_TS > query_span_ts || ef->_TE < query_span_te)//��ѯ�����䲻��EF_Index�����������
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
		string aut_name = aut_name_raw.substr(1, name_length);//ȥ������ǰ���˫����
		for (int i = 0; i < aut_name.size(); ++i)//�����������е��»����滻Ϊ�ո�
			if (aut_name[i] == '_')
			{
				aut_name[i] = ' ';
			}
		author_name_by_id[stoi(aut_id)] = aut_name;
	}
}


int map_start_time(int ts)//����ѯ������ʼʱ��ӳ��Ϊ���������ֵ
{
	return (lower_bound(consecutive_timestamp.begin(), consecutive_timestamp.end(), ts) - consecutive_timestamp.begin()) + 1;
}

int map_end_time(int te)//����ѯ������ֹʱ��ӳ��Ϊ���������ֵ
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
	int weight;//lineage node��Ȩֵ(ds�ڵ���),Ϊ�ѵ�candidate key
	int layer;//lineage node�Ĳ���(��lineage graph�еĲ���),Ϊ�ѵ�candidate key
	int nid; //lineage node ��id��,Ϊ�ѵ�value
	bool operator<(const L_HEAP_ITEM& another) const
	{
		if (layer != another.layer) return layer < another.layer; //������ͬ��������ķ�ǰ��
		return weight > another.weight;//������ͬ��Ȩֵ��ķ�ǰ��
	}
};

void wchain_partition_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	compute_layer_number(ef);
	set<L_HEAP_ITEM> heap_of_node_by_layer_number;//<key, node id>
	//��setģ��С���ѣ���lineage node�洢������֮���greedy chain generation
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ ef->lineage_graph[i].weight, ef->lineage_graph[i].layer_number, i });
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//����һ���µ�chain
		L_HEAP_ITEM top_item_in_heap = *heap_of_node_by_layer_number.begin();//�����Ѷ���Ϊchain�ĵ�һ��node
		int first_chain_node = top_item_in_heap.nid;//��ȡnode��id
		chain.push_back(first_chain_node);//����һ��node����chain��
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());//�Ƴ��Ѷ�
		int last_chain_node = first_chain_node;//last_chain_node�洢��ǰchain�����һ��node��id����ʼ��Ϊfirst_chain_node
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())//����greedy approach��������chain
		{
			//�������������last_chain_node���ڵ�node���ҵ�weight��С����һ��
			int nxt_chain_node = -1;//��¼node id
			int weight_of_nxt_chain_node = -1;//��¼weightֵ
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].weight, ef->lineage_graph[nxt_node].layer_number, nxt_node })//nxt_node���ڶ����δ������
					&&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node//nxt_node��weight����
					)
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;//���û���ҵ���˵���Ѿ�û�к��node������node��������ĳһchain
											//��ǰchain�������
			chain.push_back(nxt_chain_node);//��ǰchain����һ���ڵ�
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].weight, ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
			//����Ľڵ�Ӷ����Ƴ�
			last_chain_node = nxt_chain_node;//������ĩβ�ڵ�Ϊ������Ľڵ㣬��������
		}
		pair<int, int> TTI = { ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te };//��ȡ������������distinct core��TTI
		int ID = chain_set.size();//��ȡ����������ID��������chain_set�е��±꣬��Ϊ��ʱchain_set��size
		TTI2ID[TTI] = ID;//����������������distinct core TTI����ID��ӳ��
		chain_set.push_back(chain);//�ռ������ɵ�chain
	}

	//����chain���ɺ�����ÿ��lineage node��chain���,��elf_id
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;//Ŀǰ��ʵ������EF_Index���ر���ÿ��chain��ʲô�����ڱ���ֻ��Ϊ�˿��ӻ�
}

void chain_partition_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	compute_layer_number(ef);
	set<pair<int, int>> heap_of_node_by_layer_number;//<layer number, node id>
	//��setģ��С���ѣ���lineage node�洢������֮���greedy chain generation
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ ef->lineage_graph[i].layer_number, i });
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//����һ���µ�chain
		pair<int, int> top_item_in_heap = *heap_of_node_by_layer_number.begin();//�����Ѷ���Ϊchain�ĵ�һ��node
		int first_chain_node = top_item_in_heap.second;//��ȡnode��id
		chain.push_back(first_chain_node);//����һ��node����chain��
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());//�Ƴ��Ѷ�
		int last_chain_node = first_chain_node;//last_chain_node�洢��ǰchain�����һ��node��id����ʼ��Ϊfirst_chain_node
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())//����greedy approach��������chain
		{
			//�������������last_chain_node���ڵ�node���ҵ�weight��С����һ��
			int nxt_chain_node = -1;//��¼node id
			int weight_of_nxt_chain_node = -1;//��¼weightֵ
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].layer_number, nxt_node })//nxt_node���ڶ����δ������
					&&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node//nxt_node��weight����
					)
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;//���û���ҵ���˵���Ѿ�û�к��node������node��������ĳһchain
											//��ǰchain�������
			chain.push_back(nxt_chain_node);//��ǰchain����һ���ڵ�
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
			//����Ľڵ�Ӷ����Ƴ�
			last_chain_node = nxt_chain_node;//������ĩβ�ڵ�Ϊ������Ľڵ㣬��������
		}
		pair<int, int> TTI = { ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te };//��ȡ������������distinct core��TTI
		int ID = chain_set.size();//��ȡ����������ID��������chain_set�е��±꣬��Ϊ��ʱchain_set��size
		TTI2ID[TTI] = ID;//����������������distinct core TTI����ID��ӳ��
		chain_set.push_back(chain);//�ռ������ɵ�chain
	}

	//����chain���ɺ�����ÿ��lineage node��chain���,��elf_id
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;//Ŀǰ��ʵ������EF_Index���ر���ÿ��chain��ʲô�����ڱ���ֻ��Ϊ�˿��ӻ�
}

const int N = 10000010, M = 10000010;//����ͼ�ĵ����ͱ���,lineage graph�ĵ�������С��N,��������С��M
int h[N], e[M], ne[M], idx_bp;//���ڽӱ�洢����ͼ���ÿ������Ҳ��ھӵ㼯,idx_bp��TEL��idx����
int match[N];//���浱ǰ�Ҳ��ƥ�䵽������,δ��ƥ����Ϊ0
bool st[N];//Ѱ������·�Ĺ����м�¼�Ҳ���Ƿ���������·��

void add(int a, int b)
{
	e[idx_bp] = b, ne[idx_bp] = h[a], h[a] = idx_bp++;
}

bool find_aug_path(int x)//������x������������·,�������������·flipƥ��(match)������true,�������򷵻�false
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


vector<int> chain_set_dst[N];//�ɲ��鼯�õ���ԭʼ��С·��(chain)���Ǽ�,���chain�Ĳ��鼯����ڵ�Ϊi,��chain������chain_set_dst[i]

void chain_partition_opt(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	memset(h, -1, sizeof h);
	memset(match, -1, sizeof match);
	memset(st, false, sizeof st);
	idx_bp = 0;
	int max_match = 0;
	int vn = ef->number_of_lineage_node;//��ȡlineage graph�ڵ�����vn
	for (int lv = 0; lv < vn; ++lv)//����lineage graphÿ����(lv, rv),���������С·�����ǵĶ���ͼ
	{
		for (int rv : ef->lineage_graph[lv].nxt_nd)
		{
			add(lv, rv);//��������ͼ�еı�
		}
	}
	for (int lv = 0; lv < vn; lv++)//�����ƥ��
	{
		memset(st, false, sizeof st);
		if (find_aug_path(lv)) max_match++;
	}
	
	int cn = vn - max_match;//��С·��������,��chain����

	//��������ƥ���(��Ϊ·�������е����б�),������ͬһ·���Ľڵ㲢��ͬһ����
	init_p();//�����õ��˼��ײ��鼯,���ײ��鼯��С(VMAX)��������lineage node������СN
	for (int v = 0; v < vn; ++v)
	{
		if (match[v] == -1) continue;
		int u = match[v];
		combine(u, v);
	}

	for (int i = 0; i < N; ++i) chain_set_dst[i].clear();//���ܶ�ι���,���������chain_set_dst

	//�������BFS����lineage graph�еĽڵ����ɸ���chain,����ÿ���ڵ�u,����u���ڵļ���idΪset_id,ֱ�ӽ�u��ӵ�chain_set_dst[set_id]��ĩβ
	int* in_queue = new int[ef->number_of_lineage_node];//����һ�����飬��¼ÿ��lineage node�Ƿ������
	memset(in_queue, 0, 4 * (ef->number_of_lineage_node));//�������ʼ��Ϊȫ0
	queue<int> q;//����BFS����
	q.push(ef->entry_node_id);//��entry node���
	in_queue[ef->entry_node_id] = 1;//���entry nodeΪ�Ѿ������

	while (q.size())//BFS
	{
		int node_id = q.front();//��ȡlineage node id
		q.pop();
		int set_id = find(node_id);//��ȡlineage node���ڲ��鼯set��id
		chain_set_dst[set_id].push_back(node_id);//����lineage node�ռ�����Ӧchain
		for (auto nxt_node_id : ef->lineage_graph[node_id].nxt_nd)
		{
			if (!in_queue[nxt_node_id])
			{
				//���
				q.push(nxt_node_id);
				//���Ϊ�������
				in_queue[nxt_node_id] = 1;
			}
		}
	}
	delete[] in_queue;//�ͷ��ڴ�

	//����chain_set_dst,�ռ�����chain,����idһ����[0,N-1]��Χ��,��lineage node��id��Χ
	for (int i = 0; i < N; ++i)
	{
		if (chain_set_dst[i].size())//chain����,�ռ�chain
		{
			int fst_nd_in_chain = chain_set_dst[i][0];//��ȡchain�е�һ���ڵ��lineage node id 
			int ts = ef->lineage_graph[fst_nd_in_chain].ts;//��ȡ�ýڵ�TTI
			int te = ef->lineage_graph[fst_nd_in_chain].te;//��ȡ�ýڵ�TTI
			int ID = chain_set.size();//����chain��id��Ϊ��ǰ��chain_set��size
			TTI2ID[{ts, te}] = ID;//����ýڵ㵽chain id��ӳ��
			chain_set.push_back(chain_set_dst[i]);//�ռ�chain
		}
	}

	//����chain���ɺ�����ÿ��lineage node��chain���,��elf_id
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
	elf.v_num = number_of_vertex;//����elf�Ľڵ�������Ϊchain�е�һ��node��Ӧtkc�Ľڵ���
	for (auto vn : Mv) elf.v_raw.push_back(vn.first);//����elf�Ľڵ㼯���ڵ���Ϊԭʱ��ͼ�еı�ţ����ܲ�������
	sort(elf.v_raw.begin(), elf.v_raw.end());//elf�ڵ㼯������������ӳ�䵽elf��forest�ڵĽڵ��ţ�������
	elf.init_mem(number_of_vertex);//��ʼ��elf foreset���ڽӱ��ڴ�
	vector<vector<int>> inc_edge;//chain����������distinct core֮��������߼�,����֮�󹹽�forest
	compute_inc_edge(ef, chain, inc_edge);//��ȡchain����distinct core��������

	construct_forest(ef, elf, chain, inc_edge);

}

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
			//cntinfo[INFO::PoR]++;
			//for (int c = te - 1; c >= __te; --c)//Accumulate PoR Cell
			//	if ((*prune_flag)[ts - Ts][c - Ts] == 0)
			//(*prune_flag)[ts - Ts][c - Ts] = 1;
			te = __te;//PoR
		}
	}; //PoR
	auto sqz = [&](int __ts, int __te) {
		if (ts < __ts || te > __te) { //Overline Trigger
			cntinfo[INFO::SQZ]++;
			//if (ts < __ts) {//Accumulate PoU Cell
			//	cntinfo[INFO::PoU]++;
			//	for (int r = ts + 1; r <= __ts; ++r)
			//		for (int c = te; c >= r; --c)
			//			if ((*prune_flag)[r - Ts][c - Ts] == 0)
			//		(*prune_flag)[r - Ts][c - Ts] = 2;
			//}
			//if (__te < te) {//Accumulate PoL Cell
			//	cntinfo[INFO::PoL]++;
			//	for (int r = __ts + 1; r <= __te; ++r)
			//		for (int c = te; c > __te; --c)
			//			if ((*prune_flag)[r - Ts][c - Ts] == 0)
			//		(*prune_flag)[r - Ts][c - Ts] = 3;
			//	cntinfo[INFO::PoR]++;
			//	for (int c = te - 1; c >= __te; --c)
			//		if ((*prune_flag)[ts - Ts][c - Ts] == 0)
			//	(*prune_flag)[ts - Ts][c - Ts] = 1;
			//}
			_ts = __ts;  //PoU
			_te = __te;  //PoL
		}
	};
	auto tag = [&](int __ts)
	{
		if (ts < __ts) //Overline Triggered
		{
			cntinfo[INFO::TAG]++;
			//cntinfo[INFO::PoU]++;
			for (int r = ts + 1; r <= __ts; ++r)
			{
				if (endr.count(r) == 0)
					endr[r] = -1;
				endr[r] = max(endr[r], te + 1); //Tag for PoU
			}

			//for (int r = ts + 1; r <= __ts; ++r)//Accumulate PoU Cell
			//	for (int c = te; c >= r; --c)
			//		if ((*prune_flag)[r - Ts][c - Ts] == 0)
			//	(*prune_flag)[r - Ts][c - Ts] = 2;
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
			if (TTI2ID.find(TTI) != TTI2ID.end())//��ǰdistinct coreΪĳһchain��,����chain��MTSF
			{
				int ID = TTI2ID[TTI];
				if (ef->elf_list[ID].idx == 0) //OTCD���ܷ���ͬһ��tz��Σ�����ȷ��ELF��δ������Ź���
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
	vector<vector<int>> chain_set;//������������chain_partition_o�м��㣬ÿ�����������lineage graph�ڵ�������
	static unordered_map<pair<int, int>, int, pair_hash> TTI2ID;//����������distinct core��TTI������ŵ�ӳ�䣬����chain_partition_o�м���
	TTI2ID.clear();//ÿ�ι����µ�ELF֮ǰ��������׵���ID��ӳ�伯
	auto t0 = system_clock::now();

	chain_partition_opt(ef, chain_set, TTI2ID);//�˴���ѡchain_partition_o / wchain_partition_o / chain_partition_opt

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
	EF_Index* ef = new EF_Index(Ts, Te, K);//��ʼ��EF_Index,Ϊ���صĶ���

	auto t0 = system_clock::now();

	lg_construct(ef);

	auto t1 = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
	printf("[%d,%d,%d], lineage-graph-construction takes %lldns\n", Ts, Te, K, clapse_ns.count());

	evo_construct(ef);
	elf_construct_o(ef);
	return ef;
}

vector<int> cc_set[VMAX];//ĳ��TKC��������ͨ�����м����ݣ���ӦTKC��ͨ�ԵĲ��鼯������ڵ�Ϊv����ͨ�����洢��cc_set[v];
void get_cc_of_tkc(int Ts, int Te, int k, vector<vector<int>>& ccs)//��ȡĳ��TKC��ȫ����ͨ�����������ccs;
{
	ccs.clear();
	for (int i = 0; i < VMAX; ++i) cc_set[i].clear();//���cc_set
	//�������г�ʼ��tkc��TEL
	buildtel(Ts, Te);
	initMH(Ts, Te);
	decomp(k);
	init_p();//��ʼ�����鼯
	for (auto edge_freq : Mc)//����tkc��ͨ�ԵĲ��鼯
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)//�����鼯�д���ڵ�Ϊrv�����нڵ�洢��cc_set[rv]
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

void print_tccs_ef_clapse_per_cc(EF_Index* ef, int _ts, int _te, int _k)//���TCCS-EF��ѯTKC������ͨ��������ʱ
{
	vector<vector<int>> ccs;//TKC��ͨ�������� 
	get_cc_of_tkc(_ts, _te, _k, ccs);//��ȡTKC������ͨ����
	long long tot_clapse = 0ll;//ͳ��TCCS��ѯ������ͨ��������ʱ��
	for (int i = 0; i < ccs.size(); ++i)
	{
		vector<int> ans;
		auto t0 = system_clock::now();
		optimal_tccs(ef, _ts, _te, _k, ccs[i][0], ans);//��TCCS��ȡ���CC
		auto t1 = system_clock::now();
		auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
		tot_clapse += clapse_ns.count();
		printf("TKC(%d, %d, %d), TCCS-EF on CC-%d takes:%lld\n", _ts, _te, _k, i, tot_clapse);
	}
}

void tccs_ol(int _ts, int _te, int _k, int _v, vector<int>& ans)//��G[Ts,Te]�е���TKC,�ټ�����ͨ�Եõ���
{
	//ִ��ǰG��TEL�Ѿ����ص�TEL������ʵ����
	tcdop(_ts, _te, _k);
	init_p();//��ʼ�����鼯
	for (auto edge_freq : Mc)//����tkc��ͨ�ԵĲ��鼯
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	int pv = find(_v);
	for (auto vertex_deg : Mv)//TKC�����к�_v����ͬһ���ϵĵ㼴Ϊ��
	{
		int v = vertex_deg.first;
		if (find(v) == pv) ans.push_back(v);
	}
}

void print_tccs_ol_clapse_per_cc(int Ts, int Te, int _ts, int _te, int _k)//���TCCS-OL��ѯTKC������ͨ��������ʱ,[Ts,Te]�����ڱȽϵ�TCCS-EF��EF-Index����������ͬ
{
	vector<vector<int>> ccs;//TKC��ͨ�������� 
	get_cc_of_tkc(_ts, _te, _k, ccs);//��ȡTKC������ͨ����
	long long tot_clapse = 0ll;//ͳ��TCCS��ѯ������ͨ��������ʱ��
	for (int i = 0; i < ccs.size(); ++i)
	{
		vector<int> ans;
		buildtel(Ts, Te);
		initMH(Ts, Te);
		auto t0 = system_clock::now();
		tccs_ol(_ts, _te, _k, ccs[i][0], ans);//��TCCS��ȡ���CC
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

void ef_expand_forward(EF_Index* ef, int TE)
{
	int _TS = ef->_TS;
	int _TE = ef->_TE;
	int _K = ef->_K;
	if (TE != _TE + 1)
	{
		//������֧�ֵ������Ÿ���
		printf("TE != _TE + 1, updating request not supported\n");
		return;
	}
	
	//�������й�������TE�еĵ�һ��cell��dc,Ϊ֮��TCD��׼��
	buildtel(_TS, TE);
	initMH(_TS, TE);
	decomp(_K);

	if (tsarc[tail] != TE)//tail�����ϲ�Ӧ��Ϊ-1,����[_TS,TE]�²�����tkc,��ô�����EF_IndexӦΪ��
	{
		//���Ų������µ�tz,��EF_Index�ṹ��Ӱ��,���¹������ұ߽��ֱ�ӷ���
		ef->_TE = TE;
		return;
	}

	int largest_ts_in_nw_tz = 0;//����ts,ʹ��[ts,TE]����һ��������tz,����TCD�м�¼,���ں�������lineage relation
	vector<L_NODE> nd_of_nw_tz;//�ռ�����tz��TTI,Ϊ������б�,����lineage graph�е�i��ָ���i+1��(lineage relation, edge in lineage graph)

	//��������������һ��cell(����)ִ��TCD,��ȡ�����������
	int ts = _TS, te = TE;
	//ֻҪ��ǰcell��TTI�ұ߽���ΪTE,��˵����ǰcell[ts,te]��Ӧһ��������tz
	do {//����ѭ��ʱ,��ǰ��ds��Ӧ��һ��cell,���Ѿ�ȷ��������һ������tz

		L_NODE nw_nd;//Ϊ��tz����L_NODE
		nw_nd.ts = tsarc[head];//����L_NODE��TTI
		nw_nd.te = tsarc[tail];//����L_NODE��TTI
		nw_nd.weight = Mv.size();//����L_NODE��Ȩֵ,��Ϊds�еĽڵ���
		nd_of_nw_tz.push_back(nw_nd);//�ռ�����L_NODE

		ts = tsarc[head]; //Local Pruning,����֮��ļ���������ͬTTI��cell

		largest_ts_in_nw_tz = ts;//����largest_ts_in_nw_tz

		ts++;//ts�����������tz֮�����ڵ�һ��cell
		tcdop(ts, te, _K);//��ȡ��cell��ds
	} while(tail != -1 && head != -1 && tsarc[head] <= tsarc[tail] && tsarc[tail] == TE);
	//ǰ������ֹ����:�����е���ײ�cell���ڵ��д���֮ǰ�������,��ʱ���һ��cellΪ��cell(dsΪ��)
	//���ĸ���ֹ����:��ǰ��cell�Ѿ�����֮ǰ�е�tz,Global Pruning,������ǰ����


	//��������whileѭ�������µ�lineage node
	size_t nw_num_of_lineage_node = ef->number_of_lineage_node + nd_of_nw_tz.size();//�����µ�lineage node����(tz����)

	L_NODE* nw_lg = new L_NODE[nw_num_of_lineage_node];//Ϊ�µ�lineage graph����ռ�

	std::unordered_map<TTI, int, pair_hash> tti_to_node;//TTI��lineage node id��ӳ��
														//���ں�������zone adjacency����lineage relation

	int i = 0;
	while (i < ef->number_of_lineage_node)//�ɵ�lineage graphֱ�ӿ���
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
	while(i < nw_num_of_lineage_node)//������lineage node��ʼ��TTI��weight
	{
		nw_lg[i].ts = nd_of_nw_tz[j].ts;
		nw_lg[i].te = nd_of_nw_tz[j].te;
		nw_lg[i].weight = nd_of_nw_tz[j].weight;
		tti_to_node[{nw_lg[i].ts, nw_lg[i].te}] = i;
		i++;
		j++;
	}

	//���湹���µ�lineage relation(lineage graph�еı�)

	for (int i = 0; i < nd_of_nw_tz.size() - 1; ++i)//��������tz֮��ı�
	{
		//��ȡ��ʼ�ڵ��id
		int ts_src = nd_of_nw_tz[i].ts;
		int te_src = nd_of_nw_tz[i].te;
		int nd_src = tti_to_node[{ts_src, te_src}];

		//��ȡĿ��ڵ��id
		int ts_dst = nd_of_nw_tz[i + 1].ts;
		int te_dst = nd_of_nw_tz[i + 1].te;
		int nd_dst = tti_to_node[{ts_dst, te_dst}];

		//����±�(������)
		nw_lg[nd_src].nxt_nd.push_back(nd_dst);
		nw_lg[nd_dst].pre_nd.push_back(nd_src);
	}

	//�����_TE�н���TCD,��������tz�;�tz֮���������
	ts = _TS, te = _TE;
	buildtel(ts, te);
	initMH(ts, te);
	decomp(_K);

	do {//TE�е�һ��dsһ����һ��������ds�γ�lineage relation
		int TTI_ts = tsarc[head];
		int TTI_te = tsarc[tail];
		
		//����corner interval,[TTI_ts,TE]��Ϊһ����tz��TTI,�����������tz֮�����lineage relation
		int nd_src = tti_to_node[{TTI_ts, TE}];
		int nd_dst = tti_to_node[{TTI_ts, TTI_te}];

		//����±�(������)
		nw_lg[nd_src].nxt_nd.push_back(nd_dst);
		nw_lg[nd_dst].pre_nd.push_back(nd_src);
		ts = TTI_ts;//������TTI
		ts++;//������һ��tz
		tcdop(ts, te, _K);//��ȡ��tz��ds
	} while (tail != -1 && head != -1 && tsarc[head] <= tsarc[tail] && ts <= largest_ts_in_nw_tz);
	//ע��,largest_ts_in_nw_tz���ܴ���TE�������Ч����ʼʱ��,��ʱds������Ϊ��,ǰ����������ʹѭ������

	//�����ж�evo_map�Ƿ���Ҫ����,ֻ��Ҫ�ж����һ�������Ľڵ���û�к�̽ڵ㼴��
	int num_of_nw_tz = nd_of_nw_tz.size();//��ȡ�����ڵ������,���е���������һ������tz
	int last_nw_nd = tti_to_node[{nd_of_nw_tz[num_of_nw_tz - 1].ts, nd_of_nw_tz[num_of_nw_tz - 1].te}];//��ȡ���һ�������ڵ��id
	if (nw_lg[last_nw_nd].nxt_nd.size() == 0)//˵�����һ������nd��Ӧһ��������minimal TTI,��evo_map��
	{
		A_NODE* nw_evo = new A_NODE[ef->length_of_evo_array + 1];//����evo_array,����+1
		int i = 0;
		while (i < ef->length_of_evo_array)
		{
			nw_evo[i].ts = ef->evo_array[i].ts;
			nw_evo[i].te = ef->evo_array[i].te;
			nw_evo[i].lineage_node = ef->evo_array[i].lineage_node;
			i++;
		}

		//��������minimal TTI��evo_map��
		nw_evo[i].ts = nd_of_nw_tz[num_of_nw_tz - 1].ts;
		nw_evo[i].te = nd_of_nw_tz[num_of_nw_tz - 1].te;
		nw_evo[i].lineage_node = tti_to_node[{nw_evo[i].ts, nw_evo[i].te}];

		//�ͷžɵ�evo_array,��������Ϊ�µ�evo_array
		delete[] ef->evo_array;
		ef->evo_array = nw_evo;
		ef->length_of_evo_array = ef->length_of_evo_array + 1;//evo_array����+1
	}

	//����,lineage graph��evo_array���������
	//�ͷžɵ�lineage graph,��������Ϊ�µ�lineage graph
	delete[] ef->lineage_graph;
	ef->lineage_graph = nw_lg;

	unordered_set<int> chain_head;//�ռ���������һ��node��id

	for (auto chain : ef->chain_set)
	{
		chain_head.insert(chain[0]);
	}

	//�������ELF,�����ж�������һ��ELF���ǲ���һ������ELF
	if (nw_lg[last_nw_nd].nxt_nd.size() && chain_head.find(nw_lg[last_nw_nd].nxt_nd[0]) != chain_head.end())//��һ��node������Ϊһ���Ѵ�����������
	{
		//�������л�ȡ����ľ�chain��id
		int head_id = nw_lg[last_nw_nd].nxt_nd[0];//��ȡӦ�����chain��chain��node��id
		int elf_id = nw_lg[head_id].elf_id;//��ȡӦ����chain��chain id,ͬʱҲ��elf��id

		//��������forѭ�������ϲ������chain
		vector<int> nw_chain;//��chain
		for (int i = ef->number_of_lineage_node; i < nw_num_of_lineage_node; ++i)//i: number_of_lineage_node--nw_num_of_lineage_node��һ��ֵ��Ϊ����node��id
		{
			nw_chain.push_back(i);//�����ڵ��ȼ�����chain,��Ϊ������ǰ��
		}
		for (auto nd_id : ef->chain_set[elf_id])
		{
			nw_chain.push_back(nd_id);//����ľ�chain�Ľڵ㴦����chain�ĺ���
		}

		ef->chain_set[elf_id] = nw_chain;//����chain

		//�������ԭ�е�elf
		delete[] ef->elf_list[elf_id].elf_head;
		delete[] ef->elf_list[elf_id].elf_nbr;
		delete[] ef->elf_list[elf_id].elf_nxt;
		delete[] ef->elf_list[elf_id].elf_label;
		ef->elf_list[elf_id].idx = 0;
		ef->elf_list[elf_id].v_raw.clear();
		ef->elf_list[elf_id].v_num = 0;

		//������µ�ELF
		create_elf_of_chain(ef, elf_id, nw_chain);
	}
	else //����һ��������chain,������Ӧ��ELF
	{
		vector<int> nw_chain;//��chain
		for (int i = ef->number_of_lineage_node; i < nw_num_of_lineage_node; ++i)//i: number_of_lineage_node--nw_num_of_lineage_node��һ��ֵ��Ϊ����node��id
		{
			nw_chain.push_back(i);//�����ڵ����μ�����chain
		}

		ELF* nw_elf_list = new ELF[ef->number_of_elf + 1];//�����µ�elf_list�ռ�,����+1
		for (int i = 0; i < ef->number_of_elf; ++i)//�ƶ��������оɵ�ELF
		{
			nw_elf_list[i].elf_head = ef->elf_list[i].elf_head;
			nw_elf_list[i].elf_label = ef->elf_list[i].elf_label;
			nw_elf_list[i].elf_nbr = ef->elf_list[i].elf_nbr;
			nw_elf_list[i].elf_nxt = ef->elf_list[i].elf_nxt;
			nw_elf_list[i].idx = ef->elf_list[i].idx;
			nw_elf_list[i].v_num = ef->elf_list[i].v_num;
			nw_elf_list[i].v_raw = ef->elf_list[i].v_raw;
		}

		//�ͷžɵ�elf_list,����Ϊ�µ�elf_list
		delete[] ef->elf_list;
		ef->elf_list = nw_elf_list;

		//����������chain��ELF,idΪ�ɵ�elf_list����
		create_elf_of_chain(ef, ef->number_of_elf, nw_chain);
		ef->number_of_elf++;//elf_list����+1
		ef->chain_set.push_back(nw_chain);//��chain����chain_set

	}

	ef->entry_node_id = ef->number_of_lineage_node;//��Ȼ������tz,��ô�µ����node��Ϊ�����ĵ�һ��tz��Ӧnode,��id���Ǿ�lineage_graph�ĳ���(lineage node����)
	ef->number_of_lineage_node = nw_num_of_lineage_node;//����lineage node ����
	ef->_TE = TE;//���EF_Index�Ĺ���������µ��µ��ұ߽�TE
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
	if (gnu <= 0 || gnu % 3600)//ָ�����Ȳ��Ϸ�
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
	if (gnu < 3600 * 24)//����С��1��,�ļ���ǰ׺Ϊ XXh
	{
		int gnu_h = gnu / 3600;
		sprintf(gnu_c_str, "%d", gnu_h);
		string gnu_num(gnu_c_str);
		gnu_str = gnu_num + "h";
	}
	else//���ȳ���1��,�ļ���ǰ׺Ϊ XXd
	{
		int gnu_d = gnu / 3600 / 24;
		sprintf(gnu_c_str, "%d", gnu_d);
		string gnu_num(gnu_c_str);
		gnu_str = gnu_num + "d";
	}

	string graph_name_str(graph_name);

	string nw_graph_name_str = "./" + gnu_str + "_" + graph_name_str.substr(2);//���ļ���ΪXX(h|d)_(ԭʼ�ļ���)

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

vector<int> ccv_set[VMAX];//����ÿ��TCC�ĵ��ż�
vector<int> cct_set[VMAX];//����ÿ��TCC��ʱ�����
int cce_cnt[VMAX];//����ÿ��TCC��connection����
vector<int> cce_set[VMAX];//����ÿ��TCC��Temporal Edge����

void init_tcc_prop_set()//��ʼ��TCC������Property Set���ڶ�ÿ��TZ(Time Zone)����LS(Local Search)֮ǰ����Ҫ����
{
	for (int i = 0; i < VMAX; ++i)//��ʼ������TCC��
	{
		ccv_set[i].clear();
		cct_set[i].clear();
		cce_set[i].clear();
		cce_cnt[i] = 0;
	}
}

void compute_tcc_prop_set(ZONE tz, int k)//��ȡTime Zone��TKC��ӦTCC������Property Set, ����ΪZONE
{
	//��ȡTZ��TTI
	auto TTI = tz.first;
	int TTI_TS = TTI.first, TTI_TE = TTI.second;

	//�������г�ʼ��TKC��TEL�����������ṹ
	buildtel(TTI_TS, TTI_TE);
	initMH(TTI_TS, TTI_TE);
	decomp(k);

	//���������ȡTKC�ĸ���TCC,���浽����TCC Property Set
	//(u,v)����һ��connection�������˵�,r������ĵ������ڵ�TCC���(�����鼯����Ԫ)

	init_p();//��ʼ�����鼯
	for (auto edge_freq : Mc)//����TKC����connection,����tkc��ͨ�ԵĲ��鼯
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)//����TKC���н��,�ռ�����TCC�Ľڵ㼯
	{
		int v = vertex_deg.first;
		int r = find(v);
		ccv_set[r].push_back(v);
	}
	for (int i = head; ~i; i = tsnxt[i])//����TKC����ʱ̬��,�ռ�TCC��ʱ�����
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
	for (int i = 0; i < VMAX; ++i)//��ÿ��TCC�еĽڵ�ID��ʱ�����������,�����ҵ���С�Ľڵ��ź���С���ʱ���
	{
		if (ccv_set[i].size())
		{
			sort(ccv_set[i].begin(), ccv_set[i].end());
			sort(cct_set[i].begin(), cct_set[i].end());
		}
	}
	for (auto edge_freq : Mc)//�ٴα�������connection,����cce_cnt
	{
		//����TKC������connection,�����ڵ�TCC��connection��������1
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		int r = find(u);
		cce_cnt[r] ++;
	}
}

void compute_tcc_prop_set_c(int ts, int te, int k)//��ȡĳ��TKC��ӦTCC������Property Set, ����ΪTKC����
{
	//�������г�ʼ��TKC��TEL�����������ṹ
	buildtel(ts, te);
	initMH(ts, te);
	decomp(k);

	//���������ȡTKC�ĸ���TCC,���浽����TCC Property Set
	//(u,v)����һ��connection�������˵�,r������ĵ������ڵ�TCC���(�����鼯����Ԫ)

	init_p();//��ʼ�����鼯
	for (auto edge_freq : Mc)//����TKC����connection,����tkc��ͨ�ԵĲ��鼯
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)//����TKC���н��,�ռ�����TCC�Ľڵ㼯
	{
		int v = vertex_deg.first;
		int r = find(v);
		ccv_set[r].push_back(v);
	}
	for (int i = head; ~i; i = tsnxt[i])//����TKC����ʱ̬��,�ռ�TCC��ʱ�������ʱ��߼�
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
	for (int i = 0; i < VMAX; ++i)//��ÿ��TCC�еĽڵ�ID��ʱ�����������,�����ҵ���С�Ľڵ��ź���С���ʱ���
	{
		if (ccv_set[i].size())
		{
			sort(ccv_set[i].begin(), ccv_set[i].end());
			sort(cct_set[i].begin(), cct_set[i].end());
		}
	}
	for (auto edge_freq : Mc)//�ٴα�������connection,����cce_cnt
	{
		//����TKC������connection,�����ڵ�TCC��connection��������1
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		int r = find(u);
		cce_cnt[r] ++;
	}
}

template<typename T>
struct OPT_TCC_FOUND {
	/*** ������������Ψһȷ��һ��TCC ***/
	int TTI_TS;//TCC�ڵ���Сʱ���
	int TTI_TE;//TCC�ڵ����ʱ���
	int MIN_VERTEX;//TCC�ڵĽڵ�id����Сֵ

	/*** LS�е�ǰ����TCC��Xֵ ***/
	T x_value;
};

void LS_BURST(int k)//X=BURSTINESS��LocalSearch,��������Ϊtime zone�ļ���(zone_set),kΪTXCQ����������BURSTINESS����TCC(����Ԫ���ʾ)
{
	OPT_TCC_FOUND<double> opt_tcc_burst = {-1, -1, -1, 0.0};//���ڼ�¼LS������BURSTINESS����TCC
	for (auto tz : zone_set)//����ǰzone_set�����Ѿ�ͨ��ZPar_O��ʼ��
	{
		init_tcc_prop_set();//׼����ȡһ����TKC������TCC,����ն�Ӧ�����

		compute_tcc_prop_set(tz, k);//����TKC��TCC�����浽����Property Set

		for (int i = 0; i < VMAX; ++i)
		{
			if (ccv_set[i].size())
			{
				//��ȡ�����TCC�ı����Ԫ��
				int TTI_TS = *cct_set[i].begin();
				int TTI_TE = *(--cct_set[i].end());
				int MIN_VERTEX = *ccv_set[i].begin();
				int span_day = (consecutive_timestamp[TTI_TE - 1] - consecutive_timestamp[TTI_TS - 1]) / 86400 + 1;//����-day���ݼ���spanΪ����
				double tcc_burstiness = (double)cce_cnt[i] * 2.0 / (double)span_day;//����TCC��burstiness,ע���ĸ��Ҫ��1,��ΪTTI_TS���ܺ�TTI_TE��ͬ
				//double tcc_burstiness = (double)ccv_set[i].size() / (double)((double)TTI_TE - TTI_TS + 1.0);
				//printf("burstiness [%d, %d, %d], %.2lf\n", TTI_TS, TTI_TE, MIN_VERTEX, tcc_burstiness);

				if (opt_tcc_burst.TTI_TS == -1 || opt_tcc_burst.x_value < tcc_burstiness)//������Optimizing Query,��X����Ϊ��������,��˲��ÿ���dominating��ϵ��TCC����ο��ǵ�����
				{
					opt_tcc_burst = { TTI_TS, TTI_TE, MIN_VERTEX, tcc_burstiness };
				}

			}
		}
	}

	printf("TCC with maximum burstiness: [%d, %d, %d] \n", opt_tcc_burst.TTI_TS, opt_tcc_burst.TTI_TE, opt_tcc_burst.MIN_VERTEX);
}

struct TCC_SZ {//TCC SIZE�Ľṹ�壬���ڲ���SIZE top-kС��TCC
	int ts, te, vid;//element key,uniquely identify a TCC
	int val;
	bool operator<(const TCC_SZ& another) const//�ԡ������ȼ������ж���,����true�������ȼ������ڡ�
	{
		return val < another.val;//���Ƕ�ӦSIZEҪtop-KС��,���������Ҫһ���󶥶ѣ���valԽС���ȼ�Խ��
	}
};

void LS_SIZE(int K, int k)//X=SIZE��LocalSearch,��������Ϊtime zone�ļ���(zone_set),KΪָ������,��ȡSIZE��С��K��TCC,kΪTXCQ�е�k
{
	//priority_queue, �Ѷ�Ԫ�ؾ���������ȼ�
	priority_queue<TCC_SZ, vector<TCC_SZ>> heap_for_max_k;
	//ά������Ԫ�ص�key����,����ʵ��ȥ��,��Ϊͬһ��TCC���ܴ�������Distinct Core,���ÿ��TCCֻ����һ��
	set<pair<pair<int, int>, int>> heap_key;
	for (auto tz : zone_set)//����ǰzone_set�����Ѿ�ͨ��ZPar_O��ʼ��
	{
		auto TTI = tz.first;
		int ts = TTI.first, te = TTI.second;
		for (int i = 0; i < VMAX; ++i) ccv_set[i].clear();//���ccv_set
		//�������г�ʼ��tkc��TEL
		buildtel(ts, te);
		initMH(ts, te);
		decomp(k);
		init_p();//��ʼ�����鼯
		for (auto edge_freq : Mc)//����tkc��ͨ�ԵĲ��鼯
		{
			int u = edge_freq.first.first;
			int v = edge_freq.first.second;
			combine(u, v);
		}
		for (auto vertex_deg : Mv)//�ռ�����TCC�Ľڵ㼯,rvΪһ��TCC�Ĵ���ڵ���
		{
			int v = vertex_deg.first;
			int rv = find(v);
			ccv_set[rv].push_back(v);
		}
		for (int i = 0; i < VMAX; ++i)//��ÿ��TCC�еĽڵ�����������,�����ҵ���С�Ľڵ���
		{
			if (ccv_set[i].size())
			{
				sort(ccv_set[i].begin(), ccv_set[i].end());
			}
		}
		for (int i = head; ~i; i = tsnxt[i])//�ռ�����TCC��ʱ�����,rΪһ��TCC�Ĵ���ڵ���
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
				if (heap_key.find({ {tcc_sz.ts, tcc_sz.te}, tcc_sz.vid }) != heap_key.end())//��TCC�Ѿ��������
				{
					continue;
				}
				heap_key.insert({ {tcc_sz.ts, tcc_sz.te}, tcc_sz.vid });//���Ϊ�Ѵ����
				if (heap_for_max_k.size() < K || (heap_for_max_k.top().val > tcc_sz.val))//����Բ���K�������TCC��sizeС�ڶѶ�,����¶�
				{
					if (heap_for_max_k.size() == K) heap_for_max_k.pop();//���Ѿ���K��,�Ƴ��Ѷ�
					heap_for_max_k.push(tcc_sz);//���
				}
			}
		}
	}
}

void o_tcc_edge_list(int ts, int te, int k, int v, string file_name)
{
	init_tcc_prop_set();//׼����ȡһ����TKC������TCC,����ն�Ӧ�����
	compute_tcc_prop_set_c(ts, te, k);//����TKC��TCC�����浽����Property Set
	for (int i = 0; i < VMAX; ++i)
	{
		if (ccv_set[i].size())
		{
			if (ccv_set[i][0] == v)//ȷ��Ϊ��Ҫ��TCC���
			{
				ofstream ofile(file_name.c_str());
				ofile << "Source" << "," << "Target" << "," << "Timestamp" << "\n";
				for (int eid : cce_set[i])
				{
					ofile << arcs[eid].src << ',' << arcs[eid].dst << ',' << arcs[eid].t << '\n';
				}
				break;//ָ����TCC��Ψһ��,�����ֱ��break
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
	unordered_map<pair<int, int>, int, pair_hash> conn_stre;//����[ts,te]�¸���connection��strength
	for (int i = 0; i < arcn; ++i)//��ʼ��[ts,te]�¸���connection��strength
		if (arcs[i].t >= ts && arcs[i].t <= te)
		{
			if (conn_stre.find({ arcs[i].src, arcs[i].dst }) == conn_stre.end())
			{
				conn_stre[{arcs[i].src, arcs[i].dst}] = 0;
			}
			conn_stre[{arcs[i].src, arcs[i].dst}] ++;
		}
	vector<int> edge_list;
	for(int i = 0; i < arcn; ++ i)//��ȡ[ts,te]��connection strength��С��h������connection������ʱ̬�߼�
		if (arcs[i].t >= ts && arcs[i].t <= te)
			if (conn_stre[{arcs[i].src, arcs[i].dst}] >= h)
			{
				edge_list.push_back(i);
			}
	//����edge_list��ʼ��[ts,te]��(k,h)-core��TEL,Mc,Mv,Hv
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