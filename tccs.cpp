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

void PClapse_ZPar_O(int Ts, int Te, int k, const char* graph_name)//将TxCQ ([Ts,Te], k)的执行时间打印到终端，单位为纳秒
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

void PClapse_TXCQ_2Phase(int Ts, int Te, int k, const char* graph_name)//将TxCQ ([Ts,Te], k)的执行时间打印到终端，单位为纳秒
{
	buildtel(Ts, Te);
	initMH(Ts, Te);
	auto t_start = system_clock::now();
	ZPar_O(Ts, Te, k);
	auto t_final1 = system_clock::now();
	ZRev(X_MEANING::USER_ENGAGEMENT, X_PROPERTY::TIME_INCREASING, T_QUERY::OPTIMIZING, k, 0.6);//变更测试X的含义的时候此处需要修改参数
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
	std::unordered_map<TTI, int, pair_hash> tti_to_node;//TTI到lineage node id的映射
																		//用于后续利用zone adjacency构建lineage connection
	for (auto time_zone : zone_set)//初始化所有time zone对应的lineage node
	{
		TTI tti = time_zone.first;
		ef->lineage_graph[lineage_node_id].ts = tti.first;//初始化tti起始时刻
		ef->lineage_graph[lineage_node_id].te = tti.second;//初始化tti终止时刻
		ef->lineage_graph[lineage_node_id].weight = distinct_core_sz[tti];//初始化time zone对应distinct core节点数
		tti_to_node[tti] = lineage_node_id;//保存tti到lineage node id的映射，用于后续建边
		lineage_node_id++;
	}
	for (int node_id = 0; node_id < ef->number_of_lineage_node; ++node_id)//遍历所有lineage node建边
	{
		TTI tti = { ef->lineage_graph[node_id].ts, ef->lineage_graph[node_id].te };//获取这个node的TTI
		LTI list_of_lti = zone_set[tti];//获取这个node的LTI列表
		int number_of_connection_to_tti = list_of_lti.size() + 1;//在lineage graph中这个node前邻居节点的数量
																 //=这个time zone的lti数量+1
		sort(list_of_lti.begin(), list_of_lti.end());//把LTI按照ts从小到大排序
		for (int i = 0; i < number_of_connection_to_tti; ++i)//依次获取这个节点每个祖先邻居的TTI=time zone凹角的cell
		{
			int ts = i == number_of_connection_to_tti - 1 ? tti.first : list_of_lti[i].first - 1;
			int te = i == 0 ? tti.second : list_of_lti[i - 1].second + 1;
			if (ts < ef->_TS || te > ef->_TE) continue;//边界情况，第一个或最后一个不存在
			int prev_node_id = tti_to_node[{ts, te}];//定理正确则[ts,te]必为一个tti
			ef->lineage_graph[node_id].pre_nd.push_back(prev_node_id);//建边node_id->prev_node_id
			ef->lineage_graph[prev_node_id].nxt_nd.push_back(node_id);//建边prev_node_id->node_id
		}
	}
	ef->entry_node_id = tti_to_node[first_tti];//设置lineage graph的入口节点，first_tti在ZPar_O中记录
}

void evo_construct(EF_Index* ef)
{
	int entry_node = ef->entry_node_id;//获取lineage graph入口节点id
	int number_of_lineage_node = ef->number_of_lineage_node;//获取lineage graph的node数量
	vector<int> set_of_end_node;//用于收集lineage graph中所有出度为零的节点（极小TTI节点）
	for (int i = 0; i < number_of_lineage_node; ++i)//遍历lineage graph的所有节点进行收集
	{
		if (ef->lineage_graph[i].nxt_nd.size() == 0)
		{
			set_of_end_node.push_back(i);//如果出度为0，收集这个节点的id
		}
	}
	ef->length_of_evo_array = set_of_end_node.size();//设置evo_array的长度即为出度为零的lineage node数量
	ef->evo_array = new A_NODE[ef->length_of_evo_array];//初始化evo_array
	for (int i = 0; i < ef->length_of_evo_array; ++i)//设置每个evo_array中元素的真实值，包括TTI和lineage node的id
	{
		int end_node_id = set_of_end_node[i];//获取lineage node的id
		ef->evo_array[i].ts = ef->lineage_graph[end_node_id].ts;//设置TTI起始时刻
		ef->evo_array[i].te = ef->lineage_graph[end_node_id].te;//设置TTI终止时刻
		ef->evo_array[i].lineage_node = end_node_id;//设置lineage node 的 id
	}
	sort(ef->evo_array, ef->evo_array + ef->length_of_evo_array);//将evo_array按照起始时刻升序排序
	//由于evo_array对应的都是极小TTI，因此起始终止时刻都各不相同，且终止时刻随起始时刻单增
}

void compute_layer_number(EF_Index* ef)
{
	int* in_queue = new int[ef->number_of_lineage_node];//构建一个数组，记录每个lineage node是否入过队（已被计算）
	memset(in_queue, 0, 4 * (ef->number_of_lineage_node));//将数组初始化为全0
	queue<int> q;//构建BFS队列
	ef->lineage_graph[ef->entry_node_id].layer_number = 0;//初始化entry node的层数为第0层
	q.push(ef->entry_node_id);//将entry node入队
	in_queue[ef->entry_node_id] = 1;//设置entry node为已经入过队
	while (q.size())//BFS
	{
		int node_id = q.front();
		q.pop();
		for (auto nxt_node_id : ef->lineage_graph[node_id].nxt_nd)

			if (!in_queue[nxt_node_id])
			{
				//设置layer number为当前node的layer number + 1
				ef->lineage_graph[nxt_node_id].layer_number = ef->lineage_graph[node_id].layer_number + 1;
				//入队
				q.push(nxt_node_id);
				//标记为已处理
				in_queue[nxt_node_id] = 1;
			}
	}
	delete[] in_queue;//释放内存
}

void chain_partition(EF_Index* ef, vector<vector<int>>& chain_set)
{
	compute_layer_number(ef);
	set<pair<int, int>> heap_of_node_by_layer_number;//<layer number, node id>
	//用set模拟小顶堆，将lineage node存储，用于之后的greedy chain generation
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ef->lineage_graph[i].layer_number, i});
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//生成一条新的chain
		pair<int, int> top_item_in_heap = *heap_of_node_by_layer_number.begin();//弹出堆顶作为chain的第一个node
		int first_chain_node = top_item_in_heap.second;//获取node的id
		chain.push_back(first_chain_node);//将第一个node加入chain里
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());//移除堆顶
		int last_chain_node = first_chain_node;//last_chain_node存储当前chain的最后一个node的id，初始化为first_chain_node
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())//采用greedy approach生成整条chain
		{
			//下面遍历所有与last_chain_node相邻的node，找到weight最小的那一个
			int nxt_chain_node = -1;//记录node id
			int weight_of_nxt_chain_node = -1;//记录weight值
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].layer_number, nxt_node })//nxt_node仍在队里，尚未被覆盖
					 &&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node//nxt_node的weight更大
				   )
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;//如果没有找到，说明已经没有后继node，或后继node均已属于某一chain
											//当前chain生成完毕
			chain.push_back(nxt_chain_node);//当前chain延申一个节点
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
											//延申的节点从堆中移除
			last_chain_node = nxt_chain_node;//更新链末尾节点为新延申的节点，继续延申
		}
		chain_set.push_back(chain);//收集新生成的chain
	}

	//所有chain生成后，设置每个lineage node的chain编号,即elf_id
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;//目前真实场景下EF_Index不必保存每条chain是什么，现在保存只是为了可视化
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
	//此时tkc的structure（Mv,Hv,Mc,TEL）应该已经对应chain中第一个distinct core
	for (int i = 0; i < chain.size() - 1; ++i)
	{
		int ts_of_target_tti = ef->lineage_graph[chain[i + 1]].ts;
		int te_of_target_tti = ef->lineage_graph[chain[i + 1]].te;
		vector<int> tcd_dec_edge;//收集tcd过程中减少的时序边
		tcd_edge_collect(ts_of_target_tti, te_of_target_tti, ef->_K, tcd_dec_edge);
		inc_edge.push_back(tcd_dec_edge);//chain中第i个distinct core到第i + 1给distinct core减少的时序边
	}
	inc_edge.push_back({});//加入最后一个边集(初始为空),用于保存chain中最后一个distinct core的时序边
	//chain中最后一个distinct core的所有时序边即为其增量边，全部保存
	int x = chain.size() - 1;//最后一个distinct core所在的下标
	for (int p = head; p != -1; p = tsnxt[p])//收集TEL里剩下的所有时序边，先遍历TL，再遍历每个TL[t]链上的时序边
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
	for (int i = 0; i < elf.v_num; ++i) p[i] = i;//初始化并查集，用于forest构建(ELF forest点编号:0-(v_num-1))
	for (int i = n; i >= 0; --i)
	{
		for (int eid : inc_edge[i])
		{
			int raw_src = arcs[eid].src;
			int raw_dst = arcs[eid].dst;
			int elf_src = elf.elf_vertex_id(raw_src);
			int elf_dst = elf.elf_vertex_id(raw_dst);
			if (find(elf_src) != find(elf_dst))//如果两个点在ELF forest中还不连通，则在forest中添加这条边
			{
				elf.insert_edge(elf_src, elf_dst, ef->lineage_graph[chain[i]].ts, ef->lineage_graph[chain[i]].te);
				combine(elf_src, elf_dst);//维护并查集，两个端点连通
			}
		}
	}
}

void create_elf_of_chain(EF_Index* ef, int elf_id, vector<int>& chain)
{
	ELF& elf = ef->elf_list[elf_id];

	init_tkc_structure(ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te, ef->_K);

	size_t number_of_vertex = Mv.size();
	elf.v_num = number_of_vertex;//设置elf的节点数，即为chain中第一个node对应tkc的节点数
	for (auto vn : Mv) elf.v_raw.push_back(vn.first);//设置elf的节点集（节点编号为原时序图中的编号，可能不连续）
	sort(elf.v_raw.begin(), elf.v_raw.end());//elf节点集升序排序，用于映射到elf的forest内的节点编号（连续）
	elf.init_mem(number_of_vertex);//初始化elf foreset的邻接表内存
	vector<vector<int>> inc_edge;//chain上相邻两个distinct core之间的增量边集,用于之后构建forest
	compute_inc_edge(ef, chain, inc_edge);//获取chain相邻distinct core的增量边

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
	//在elf_construct里这TTI2ID只是为了兼容chain_partition_opt而创建,后面调用的是create_elf而非create_elf_o,因此没有实际作用
	static unordered_map<pair<int, int>, int, pair_hash> TTI2ID;//所有链链首distinct core的TTI到链编号的映射，会在chain_partition_o中计算
	TTI2ID.clear();//每次构建新的ELF之前先清空链首到链ID的映射集
	
	vector<vector<int>> chain_set;
	chain_partition_opt(ef, chain_set, TTI2ID);
	create_elf(ef, chain_set);
}

EF_Index* ef_construct(int Ts, int Te, int K)
{
	EF_Index* ef = new EF_Index(Ts, Te, K);//初始化EF_Index,为返回的对象
	lg_construct(ef);
	evo_construct(ef);
	elf_construct(ef);
	return ef;
}

int recover_ts(int t)//将连续的时间戳复原为原图中离散的时间戳,t必须在连续化后的时间戳范围内
{
	if (t > consecutive_timestamp.size() || t < 1)
	{
		printf("timestamp out of range\n");
		return -1;
	}
	t = consecutive_timestamp[t - 1];
	return t;
}

void ef_dump_chain_set(EF_Index* ef)//打印EF_Index的所有chain,TTI为原图时间,并计算开销
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

void ef_calc_tot_heap(EF_Index* ef)//计算EF_Index分配的总堆内存
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

void ef_calc_lg_width(EF_Index* ef)//计算EF_Index的lineage graph最宽层包含的节点数
{
	unordered_map<int, int> num_of_nd_per_layer;//统计lineage graph每层节点数
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

void ef_dump(EF_Index* ef)//打印一个EF_Index的相关信息
{
	printf("Properties of EF_Index under ([%d,%d],%d)\n", recover_ts(ef->_TS), recover_ts(ef->_TE), ef->_K);
	printf("The number of lineage node is %d\n", ef->number_of_lineage_node);
	printf("The number of ELF instances is %d\n", ef->number_of_elf);
	printf("The number of elements in evo-array is %d\n", ef->length_of_evo_array);

	int tot_lg_edge = 0;//统计lineage relation的总数，即为lineage graph的总边数

	for (int i = 0; i < ef->number_of_lineage_node; ++i)//遍历lineage graph的所有节点，累加各个节点的出边数目
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
	if (ef->_K != query_k)//查询的k和EF_Index不匹配
	{
		printf("The K value of the EF_Index does not match the query k\n");
		return;
	}
	if (ef->_TS > query_span_ts || ef->_TE < query_span_te)//查询的区间不在EF_Index构造的区间内
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
		string aut_name = aut_name_raw.substr(1, name_length);//去除人名前后的双引号
		for (int i = 0; i < aut_name.size(); ++i)//将所有人名中的下划线替换为空格
			if (aut_name[i] == '_')
			{
				aut_name[i] = ' ';
			}
		author_name_by_id[stoi(aut_id)] = aut_name;
	}
}


int map_start_time(int ts)//将查询区间起始时刻映射为连续化后的值
{
	return (lower_bound(consecutive_timestamp.begin(), consecutive_timestamp.end(), ts) - consecutive_timestamp.begin()) + 1;
}

int map_end_time(int te)//将查询区间终止时刻映射为连续化后的值
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
	int weight;//lineage node的权值(ds节点数),为堆的candidate key
	int layer;//lineage node的层数(在lineage graph中的层数),为堆的candidate key
	int nid; //lineage node 的id号,为堆的value
	bool operator<(const L_HEAP_ITEM& another) const
	{
		if (layer != another.layer) return layer < another.layer; //层数不同，层数大的放前面
		return weight > another.weight;//层数相同，权值大的放前面
	}
};

void wchain_partition_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	compute_layer_number(ef);
	set<L_HEAP_ITEM> heap_of_node_by_layer_number;//<key, node id>
	//用set模拟小顶堆，将lineage node存储，用于之后的greedy chain generation
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ ef->lineage_graph[i].weight, ef->lineage_graph[i].layer_number, i });
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//生成一条新的chain
		L_HEAP_ITEM top_item_in_heap = *heap_of_node_by_layer_number.begin();//弹出堆顶作为chain的第一个node
		int first_chain_node = top_item_in_heap.nid;//获取node的id
		chain.push_back(first_chain_node);//将第一个node加入chain里
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());//移除堆顶
		int last_chain_node = first_chain_node;//last_chain_node存储当前chain的最后一个node的id，初始化为first_chain_node
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())//采用greedy approach生成整条chain
		{
			//下面遍历所有与last_chain_node相邻的node，找到weight最小的那一个
			int nxt_chain_node = -1;//记录node id
			int weight_of_nxt_chain_node = -1;//记录weight值
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].weight, ef->lineage_graph[nxt_node].layer_number, nxt_node })//nxt_node仍在队里，尚未被覆盖
					&&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node//nxt_node的weight更大
					)
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;//如果没有找到，说明已经没有后继node，或后继node均已属于某一chain
											//当前chain生成完毕
			chain.push_back(nxt_chain_node);//当前chain延申一个节点
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].weight, ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
			//延申的节点从堆中移除
			last_chain_node = nxt_chain_node;//更新链末尾节点为新延申的节点，继续延申
		}
		pair<int, int> TTI = { ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te };//获取这条新链链首distinct core的TTI
		int ID = chain_set.size();//获取这条新链的ID，即它在chain_set中的下标，即为此时chain_set的size
		TTI2ID[TTI] = ID;//保存这条新链链首distinct core TTI到链ID的映射
		chain_set.push_back(chain);//收集新生成的chain
	}

	//所有chain生成后，设置每个lineage node的chain编号,即elf_id
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;//目前真实场景下EF_Index不必保存每条chain是什么，现在保存只是为了可视化
}

void chain_partition_o(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	compute_layer_number(ef);
	set<pair<int, int>> heap_of_node_by_layer_number;//<layer number, node id>
	//用set模拟小顶堆，将lineage node存储，用于之后的greedy chain generation
	for (int i = 0; i < ef->number_of_lineage_node; ++i)
	{
		heap_of_node_by_layer_number.insert({ ef->lineage_graph[i].layer_number, i });
	}
	while (heap_of_node_by_layer_number.size())
	{
		vector<int> chain;//生成一条新的chain
		pair<int, int> top_item_in_heap = *heap_of_node_by_layer_number.begin();//弹出堆顶作为chain的第一个node
		int first_chain_node = top_item_in_heap.second;//获取node的id
		chain.push_back(first_chain_node);//将第一个node加入chain里
		heap_of_node_by_layer_number.erase(heap_of_node_by_layer_number.begin());//移除堆顶
		int last_chain_node = first_chain_node;//last_chain_node存储当前chain的最后一个node的id，初始化为first_chain_node
		while (ef->lineage_graph[last_chain_node].nxt_nd.size())//采用greedy approach生成整条chain
		{
			//下面遍历所有与last_chain_node相邻的node，找到weight最小的那一个
			int nxt_chain_node = -1;//记录node id
			int weight_of_nxt_chain_node = -1;//记录weight值
			for (auto nxt_node : ef->lineage_graph[last_chain_node].nxt_nd)
			{
				if (
					heap_of_node_by_layer_number.count({ ef->lineage_graph[nxt_node].layer_number, nxt_node })//nxt_node仍在队里，尚未被覆盖
					&&
					ef->lineage_graph[nxt_node].weight > weight_of_nxt_chain_node//nxt_node的weight更大
					)
				{
					nxt_chain_node = nxt_node;
					weight_of_nxt_chain_node = ef->lineage_graph[nxt_node].weight;
				}
			}
			if (nxt_chain_node == -1) break;//如果没有找到，说明已经没有后继node，或后继node均已属于某一chain
											//当前chain生成完毕
			chain.push_back(nxt_chain_node);//当前chain延申一个节点
			heap_of_node_by_layer_number.erase({ ef->lineage_graph[nxt_chain_node].layer_number, nxt_chain_node });
			//延申的节点从堆中移除
			last_chain_node = nxt_chain_node;//更新链末尾节点为新延申的节点，继续延申
		}
		pair<int, int> TTI = { ef->lineage_graph[chain[0]].ts, ef->lineage_graph[chain[0]].te };//获取这条新链链首distinct core的TTI
		int ID = chain_set.size();//获取这条新链的ID，即它在chain_set中的下标，即为此时chain_set的size
		TTI2ID[TTI] = ID;//保存这条新联链首distinct core TTI到链ID的映射
		chain_set.push_back(chain);//收集新生成的chain
	}

	//所有chain生成后，设置每个lineage node的chain编号,即elf_id
	for (int chain_id = 0; chain_id < chain_set.size(); ++chain_id)
	{
		for (int node_id : chain_set[chain_id])
		{
			ef->lineage_graph[node_id].elf_id = chain_id;
		}
	}

	ef->chain_set = chain_set;//目前真实场景下EF_Index不必保存每条chain是什么，现在保存只是为了可视化
}

const int N = 10000010, M = 10000010;//二分图的点数和边数,lineage graph的点数必须小于N,边数必须小于M
int h[N], e[M], ne[M], idx_bp;//用邻接表存储二分图左侧每个点的右侧邻居点集,idx_bp与TEL的idx区分
int match[N];//保存当前右侧点匹配到的左侧点,未被匹配则为0
bool st[N];//寻找增广路的过程中记录右侧点是否已在增广路中

void add(int a, int b)
{
	e[idx_bp] = b, ne[idx_bp] = h[a], h[a] = idx_bp++;
}

bool find_aug_path(int x)//从左侧点x出发搜索增广路,存在则根据增广路flip匹配(match)并返回true,不存在则返回false
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


vector<int> chain_set_dst[N];//由并查集得到的原始最小路径(chain)覆盖集,如果chain的并查集代表节点为i,则chain保存在chain_set_dst[i]

void chain_partition_opt(EF_Index* ef, vector<vector<int>>& chain_set, unordered_map<pair<int, int>, int, pair_hash>& TTI2ID)
{
	memset(h, -1, sizeof h);
	memset(match, -1, sizeof match);
	memset(st, false, sizeof st);
	idx_bp = 0;
	int max_match = 0;
	int vn = ef->number_of_lineage_node;//获取lineage graph节点数量vn
	for (int lv = 0; lv < vn; ++lv)//遍历lineage graph每条边(lv, rv),构造求解最小路径覆盖的二分图
	{
		for (int rv : ef->lineage_graph[lv].nxt_nd)
		{
			add(lv, rv);//建立二分图中的边
		}
	}
	for (int lv = 0; lv < vn; lv++)//求最大匹配
	{
		memset(st, false, sizeof st);
		if (find_aug_path(lv)) max_match++;
	}
	
	int cn = vn - max_match;//最小路径覆盖数,即chain数量

	//遍历所有匹配边(即为路径覆盖中的所有边),将属于同一路径的节点并入同一集合
	init_p();//这里用到了简易并查集,简易并查集大小(VMAX)不能少于lineage node数量大小N
	for (int v = 0; v < vn; ++v)
	{
		if (match[v] == -1) continue;
		int u = match[v];
		combine(u, v);
	}

	for (int i = 0; i < N; ++i) chain_set_dst[i].clear();//可能多次构造,必须先清空chain_set_dst

	//下面逐层BFS遍历lineage graph中的节点生成各条chain,对于每个节点u,假设u所在的集合id为set_id,直接将u添加到chain_set_dst[set_id]的末尾
	int* in_queue = new int[ef->number_of_lineage_node];//构建一个数组，记录每个lineage node是否入过队
	memset(in_queue, 0, 4 * (ef->number_of_lineage_node));//将数组初始化为全0
	queue<int> q;//构建BFS队列
	q.push(ef->entry_node_id);//将entry node入队
	in_queue[ef->entry_node_id] = 1;//标记entry node为已经入过队

	while (q.size())//BFS
	{
		int node_id = q.front();//获取lineage node id
		q.pop();
		int set_id = find(node_id);//获取lineage node所在并查集set的id
		chain_set_dst[set_id].push_back(node_id);//将改lineage node收集到对应chain
		for (auto nxt_node_id : ef->lineage_graph[node_id].nxt_nd)
		{
			if (!in_queue[nxt_node_id])
			{
				//入队
				q.push(nxt_node_id);
				//标记为已入过队
				in_queue[nxt_node_id] = 1;
			}
		}
	}
	delete[] in_queue;//释放内存

	//遍历chain_set_dst,收集所有chain,集合id一定在[0,N-1]范围内,即lineage node的id范围
	for (int i = 0; i < N; ++i)
	{
		if (chain_set_dst[i].size())//chain存在,收集chain
		{
			int fst_nd_in_chain = chain_set_dst[i][0];//获取chain中第一个节点的lineage node id 
			int ts = ef->lineage_graph[fst_nd_in_chain].ts;//获取该节点TTI
			int te = ef->lineage_graph[fst_nd_in_chain].te;//获取该节点TTI
			int ID = chain_set.size();//这条chain的id即为当前的chain_set的size
			TTI2ID[{ts, te}] = ID;//保存该节点到chain id的映射
			chain_set.push_back(chain_set_dst[i]);//收集chain
		}
	}

	//所有chain生成后，设置每个lineage node的chain编号,即elf_id
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
	elf.v_num = number_of_vertex;//设置elf的节点数，即为chain中第一个node对应tkc的节点数
	for (auto vn : Mv) elf.v_raw.push_back(vn.first);//设置elf的节点集（节点编号为原时序图中的编号，可能不连续）
	sort(elf.v_raw.begin(), elf.v_raw.end());//elf节点集升序排序，用于映射到elf的forest内的节点编号（连续）
	elf.init_mem(number_of_vertex);//初始化elf foreset的邻接表内存
	vector<vector<int>> inc_edge;//chain上相邻两个distinct core之间的增量边集,用于之后构建forest
	compute_inc_edge(ef, chain, inc_edge);//获取chain相邻distinct core的增量边

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
			if (TTI2ID.find(TTI) != TTI2ID.end())//当前distinct core为某一chain首,生成chain的MTSF
			{
				int ID = TTI2ID[TTI];
				if (ef->elf_list[ID].idx == 0) //OTCD可能访问同一个tz多次，必须确定ELF仍未被构造才构造
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
	vector<vector<int>> chain_set;//所有链，会在chain_partition_o中计算，每个链保存的是lineage graph节点编号序列
	static unordered_map<pair<int, int>, int, pair_hash> TTI2ID;//所有链链首distinct core的TTI到链编号的映射，会在chain_partition_o中计算
	TTI2ID.clear();//每次构建新的ELF之前先清空链首到链ID的映射集
	auto t0 = system_clock::now();

	chain_partition_opt(ef, chain_set, TTI2ID);//此处可选chain_partition_o / wchain_partition_o / chain_partition_opt

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
	EF_Index* ef = new EF_Index(Ts, Te, K);//初始化EF_Index,为返回的对象

	auto t0 = system_clock::now();

	lg_construct(ef);

	auto t1 = system_clock::now();
	auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
	printf("[%d,%d,%d], lineage-graph-construction takes %lldns\n", Ts, Te, K, clapse_ns.count());

	evo_construct(ef);
	elf_construct_o(ef);
	return ef;
}

vector<int> cc_set[VMAX];//某个TKC的所有连通分量中间数据，对应TKC连通性的并查集，代表节点为v的连通分量存储在cc_set[v];
void get_cc_of_tkc(int Ts, int Te, int k, vector<vector<int>>& ccs)//或取某个TKC的全部连通分量，输出到ccs;
{
	ccs.clear();
	for (int i = 0; i < VMAX; ++i) cc_set[i].clear();//清空cc_set
	//下面三行初始化tkc的TEL
	buildtel(Ts, Te);
	initMH(Ts, Te);
	decomp(k);
	init_p();//初始化并查集
	for (auto edge_freq : Mc)//构建tkc连通性的并查集
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)//将并查集中代表节点为rv的所有节点存储到cc_set[rv]
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

void print_tccs_ef_clapse_per_cc(EF_Index* ef, int _ts, int _te, int _k)//输出TCCS-EF查询TKC各个连通分量的用时
{
	vector<vector<int>> ccs;//TKC连通分量集合 
	get_cc_of_tkc(_ts, _te, _k, ccs);//获取TKC所有连通分量
	long long tot_clapse = 0ll;//统计TCCS查询各个连通分量的总时间
	for (int i = 0; i < ccs.size(); ++i)
	{
		vector<int> ans;
		auto t0 = system_clock::now();
		optimal_tccs(ef, _ts, _te, _k, ccs[i][0], ans);//用TCCS获取这个CC
		auto t1 = system_clock::now();
		auto clapse_ns = duration_cast<nanoseconds>(t1 - t0);
		tot_clapse += clapse_ns.count();
		printf("TKC(%d, %d, %d), TCCS-EF on CC-%d takes:%lld\n", _ts, _te, _k, i, tot_clapse);
	}
}

void tccs_ol(int _ts, int _te, int _k, int _v, vector<int>& ans)//从G[Ts,Te]中导出TKC,再计算连通性得到答案
{
	//执行前G的TEL已经加载到TEL的运行实例中
	tcdop(_ts, _te, _k);
	init_p();//初始化并查集
	for (auto edge_freq : Mc)//构建tkc连通性的并查集
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	int pv = find(_v);
	for (auto vertex_deg : Mv)//TKC中所有和_v处于同一集合的点即为答案
	{
		int v = vertex_deg.first;
		if (find(v) == pv) ans.push_back(v);
	}
}

void print_tccs_ol_clapse_per_cc(int Ts, int Te, int _ts, int _te, int _k)//输出TCCS-OL查询TKC各个连通分量的用时,[Ts,Te]与用于比较的TCCS-EF的EF-Index构造区间相同
{
	vector<vector<int>> ccs;//TKC连通分量集合 
	get_cc_of_tkc(_ts, _te, _k, ccs);//获取TKC所有连通分量
	long long tot_clapse = 0ll;//统计TCCS查询各个连通分量的总时间
	for (int i = 0; i < ccs.size(); ++i)
	{
		vector<int> ans;
		buildtel(Ts, Te);
		initMH(Ts, Te);
		auto t0 = system_clock::now();
		tccs_ol(_ts, _te, _k, ccs[i][0], ans);//用TCCS获取这个CC
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
		//方法仅支持单步扩张更新
		printf("TE != _TE + 1, updating request not supported\n");
		return;
	}
	
	//下面三行构造新增TE列的第一个cell的dc,为之后TCD做准备
	buildtel(_TS, TE);
	initMH(_TS, TE);
	decomp(_K);

	if (tsarc[tail] != TE)//tail理论上不应该为-1,否则[_TS,TE]下不存在tkc,那么传入的EF_Index应为空
	{
		//扩张不产生新的tz,对EF_Index结构无影响,更新构造跨度右边界后直接返回
		ef->_TE = TE;
		return;
	}

	int largest_ts_in_nw_tz = 0;//最大的ts,使得[ts,TE]属于一个新增的tz,会在TCD中记录,用于后续构建lineage relation
	vector<L_NODE> nd_of_nw_tz;//收集新增tz的TTI,为有序的列表,在新lineage graph中第i项指向第i+1项(lineage relation, edge in lineage graph)

	//接下来对新增的一列cell(区间)执行TCD,获取上面两个结果
	int ts = _TS, te = TE;
	//只要当前cell的TTI右边界仍为TE,则说明当前cell[ts,te]对应一个新增的tz
	do {//进入循环时,当前的ds对应第一个cell,且已经确定其属于一个新增tz

		L_NODE nw_nd;//为新tz创建L_NODE
		nw_nd.ts = tsarc[head];//设置L_NODE的TTI
		nw_nd.te = tsarc[tail];//设置L_NODE的TTI
		nw_nd.weight = Mv.size();//设置L_NODE的权值,即为ds中的节点数
		nd_of_nw_tz.push_back(nw_nd);//收集新增L_NODE

		ts = tsarc[head]; //Local Pruning,跳过之后的几个具有相同TTI的cell

		largest_ts_in_nw_tz = ts;//更新largest_ts_in_nw_tz

		ts++;//ts进入这个新增tz之后相邻的一个cell
		tcdop(ts, te, _K);//获取新cell的ds
	} while(tail != -1 && head != -1 && tsarc[head] <= tsarc[tail] && tsarc[tail] == TE);
	//前三个终止条件:新增列的最底部cell所在的行大于之前的最大行,这时最后一个cell为灰cell(ds为空)
	//第四个终止条件:当前的cell已经并入之前列的tz,Global Pruning,更新提前结束


	//下面两重while循环构建新的lineage node
	size_t nw_num_of_lineage_node = ef->number_of_lineage_node + nd_of_nw_tz.size();//计算新的lineage node总数(tz总数)

	L_NODE* nw_lg = new L_NODE[nw_num_of_lineage_node];//为新的lineage graph分配空间

	std::unordered_map<TTI, int, pair_hash> tti_to_node;//TTI到lineage node id的映射
														//用于后续利用zone adjacency构建lineage relation

	int i = 0;
	while (i < ef->number_of_lineage_node)//旧的lineage graph直接拷贝
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
	while(i < nw_num_of_lineage_node)//新增的lineage node初始化TTI和weight
	{
		nw_lg[i].ts = nd_of_nw_tz[j].ts;
		nw_lg[i].te = nd_of_nw_tz[j].te;
		nw_lg[i].weight = nd_of_nw_tz[j].weight;
		tti_to_node[{nw_lg[i].ts, nw_lg[i].te}] = i;
		i++;
		j++;
	}

	//下面构建新的lineage relation(lineage graph中的边)

	for (int i = 0; i < nd_of_nw_tz.size() - 1; ++i)//构建新增tz之间的边
	{
		//获取起始节点的id
		int ts_src = nd_of_nw_tz[i].ts;
		int te_src = nd_of_nw_tz[i].te;
		int nd_src = tti_to_node[{ts_src, te_src}];

		//获取目标节点的id
		int ts_dst = nd_of_nw_tz[i + 1].ts;
		int te_dst = nd_of_nw_tz[i + 1].te;
		int nd_dst = tti_to_node[{ts_dst, te_dst}];

		//添加新边(正反向)
		nw_lg[nd_src].nxt_nd.push_back(nd_dst);
		nw_lg[nd_dst].pre_nd.push_back(nd_src);
	}

	//下面对_TE列进行TCD,构建新增tz和旧tz之间的新增边
	ts = _TS, te = _TE;
	buildtel(ts, te);
	initMH(ts, te);
	decomp(_K);

	do {//TE列第一个ds一定和一个新增的ds形成lineage relation
		int TTI_ts = tsarc[head];
		int TTI_te = tsarc[tail];
		
		//根据corner interval,[TTI_ts,TE]必为一个新tz的TTI,且它和这个旧tz之间具有lineage relation
		int nd_src = tti_to_node[{TTI_ts, TE}];
		int nd_dst = tti_to_node[{TTI_ts, TTI_te}];

		//添加新边(正反向)
		nw_lg[nd_src].nxt_nd.push_back(nd_dst);
		nw_lg[nd_dst].pre_nd.push_back(nd_src);
		ts = TTI_ts;//缩紧到TTI
		ts++;//进入下一个tz
		tcdop(ts, te, _K);//获取新tz的ds
	} while (tail != -1 && head != -1 && tsarc[head] <= tsarc[tail] && ts <= largest_ts_in_nw_tz);
	//注意,largest_ts_in_nw_tz可能大于TE列最大有效的起始时刻,这时ds会最终为空,前三个条件将使循环结束

	//下面判断evo_map是否需要更新,只需要判断最后一个新增的节点有没有后继节点即可
	int num_of_nw_tz = nd_of_nw_tz.size();//获取新增节点的数量,运行到此至少有一个新增tz
	int last_nw_nd = tti_to_node[{nd_of_nw_tz[num_of_nw_tz - 1].ts, nd_of_nw_tz[num_of_nw_tz - 1].te}];//获取最后一个新增节点的id
	if (nw_lg[last_nw_nd].nxt_nd.size() == 0)//说明最后一个新增nd对应一个新增的minimal TTI,即evo_map项
	{
		A_NODE* nw_evo = new A_NODE[ef->length_of_evo_array + 1];//分配evo_array,长度+1
		int i = 0;
		while (i < ef->length_of_evo_array)
		{
			nw_evo[i].ts = ef->evo_array[i].ts;
			nw_evo[i].te = ef->evo_array[i].te;
			nw_evo[i].lineage_node = ef->evo_array[i].lineage_node;
			i++;
		}

		//设置新增minimal TTI的evo_map项
		nw_evo[i].ts = nd_of_nw_tz[num_of_nw_tz - 1].ts;
		nw_evo[i].te = nd_of_nw_tz[num_of_nw_tz - 1].te;
		nw_evo[i].lineage_node = tti_to_node[{nw_evo[i].ts, nw_evo[i].te}];

		//释放旧的evo_array,重新设置为新的evo_array
		delete[] ef->evo_array;
		ef->evo_array = nw_evo;
		ef->length_of_evo_array = ef->length_of_evo_array + 1;//evo_array长度+1
	}

	//至此,lineage graph和evo_array均更新完毕
	//释放旧的lineage graph,重新设置为新的lineage graph
	delete[] ef->lineage_graph;
	ef->lineage_graph = nw_lg;

	unordered_set<int> chain_head;//收集所有链第一个node的id

	for (auto chain : ef->chain_set)
	{
		chain_head.insert(chain[0]);
	}

	//下面更新ELF,首先判断是新增一个ELF还是并入一个已有ELF
	if (nw_lg[last_nw_nd].nxt_nd.size() && chain_head.find(nw_lg[last_nw_nd].nxt_nd[0]) != chain_head.end())//下一个node存在且为一个已存在链的链首
	{
		//下面两行获取并入的旧chain的id
		int head_id = nw_lg[last_nw_nd].nxt_nd[0];//获取应并入的chain的chain首node的id
		int elf_id = nw_lg[head_id].elf_id;//获取应并入chain的chain id,同时也是elf的id

		//下面两重for循环构建合并后的新chain
		vector<int> nw_chain;//新chain
		for (int i = ef->number_of_lineage_node; i < nw_num_of_lineage_node; ++i)//i: number_of_lineage_node--nw_num_of_lineage_node这一段值即为新增node的id
		{
			nw_chain.push_back(i);//新增节点先加入新chain,因为它们在前面
		}
		for (auto nd_id : ef->chain_set[elf_id])
		{
			nw_chain.push_back(nd_id);//并入的旧chain的节点处于新chain的后面
		}

		ef->chain_set[elf_id] = nw_chain;//更新chain

		//下面清空原有的elf
		delete[] ef->elf_list[elf_id].elf_head;
		delete[] ef->elf_list[elf_id].elf_nbr;
		delete[] ef->elf_list[elf_id].elf_nxt;
		delete[] ef->elf_list[elf_id].elf_label;
		ef->elf_list[elf_id].idx = 0;
		ef->elf_list[elf_id].v_raw.clear();
		ef->elf_list[elf_id].v_num = 0;

		//最后构造新的ELF
		create_elf_of_chain(ef, elf_id, nw_chain);
	}
	else //新增一条独立的chain,构建相应的ELF
	{
		vector<int> nw_chain;//新chain
		for (int i = ef->number_of_lineage_node; i < nw_num_of_lineage_node; ++i)//i: number_of_lineage_node--nw_num_of_lineage_node这一段值即为新增node的id
		{
			nw_chain.push_back(i);//新增节点依次加入新chain
		}

		ELF* nw_elf_list = new ELF[ef->number_of_elf + 1];//分配新的elf_list空间,长度+1
		for (int i = 0; i < ef->number_of_elf; ++i)//移动复制所有旧的ELF
		{
			nw_elf_list[i].elf_head = ef->elf_list[i].elf_head;
			nw_elf_list[i].elf_label = ef->elf_list[i].elf_label;
			nw_elf_list[i].elf_nbr = ef->elf_list[i].elf_nbr;
			nw_elf_list[i].elf_nxt = ef->elf_list[i].elf_nxt;
			nw_elf_list[i].idx = ef->elf_list[i].idx;
			nw_elf_list[i].v_num = ef->elf_list[i].v_num;
			nw_elf_list[i].v_raw = ef->elf_list[i].v_raw;
		}

		//释放旧的elf_list,设置为新的elf_list
		delete[] ef->elf_list;
		ef->elf_list = nw_elf_list;

		//构造新增的chain的ELF,id为旧的elf_list长度
		create_elf_of_chain(ef, ef->number_of_elf, nw_chain);
		ef->number_of_elf++;//elf_list长度+1
		ef->chain_set.push_back(nw_chain);//新chain加入chain_set

	}

	ef->entry_node_id = ef->number_of_lineage_node;//既然有新增tz,那么新的入口node必为新增的第一个tz对应node,其id就是旧lineage_graph的长度(lineage node数量)
	ef->number_of_lineage_node = nw_num_of_lineage_node;//更新lineage node 数量
	ef->_TE = TE;//最后EF_Index的构造区间更新到新的右边界TE
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
	if (gnu <= 0 || gnu % 3600)//指定粒度不合法
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
	if (gnu < 3600 * 24)//粒度小于1天,文件名前缀为 XXh
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

	string nw_graph_name_str = "./" + gnu_str + "_" + graph_name_str.substr(2);//新文件名为XX(h|d)_(原始文件名)

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

vector<int> ccv_set[VMAX];//保存每个TCC的点编号集
vector<int> cct_set[VMAX];//保存每个TCC的时间戳集
int cce_cnt[VMAX];//保存每个TCC的connection数量
vector<int> cce_set[VMAX];//保存每个TCC的Temporal Edge集合

void init_tcc_prop_set()//初始化TCC的三个Property Set，在对每个TZ(Time Zone)进行LS(Local Search)之前都需要调用
{
	for (int i = 0; i < VMAX; ++i)//初始化各个TCC的
	{
		ccv_set[i].clear();
		cct_set[i].clear();
		cce_set[i].clear();
		cce_cnt[i] = 0;
	}
}

void compute_tcc_prop_set(ZONE tz, int k)//获取Time Zone的TKC对应TCC的三个Property Set, 输入为ZONE
{
	//获取TZ的TTI
	auto TTI = tz.first;
	int TTI_TS = TTI.first, TTI_TE = TTI.second;

	//下面三行初始化TKC的TEL和三个辅助结构
	buildtel(TTI_TS, TTI_TE);
	initMH(TTI_TS, TTI_TE);
	decomp(k);

	//下面代码块获取TKC的各个TCC,保存到三个TCC Property Set
	//(u,v)代表一个connection的两个端点,r代表处理的点或边所在的TCC编号(即并查集代表元)

	init_p();//初始化并查集
	for (auto edge_freq : Mc)//遍历TKC所有connection,构建tkc连通性的并查集
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)//遍历TKC所有结点,收集所有TCC的节点集
	{
		int v = vertex_deg.first;
		int r = find(v);
		ccv_set[r].push_back(v);
	}
	for (int i = head; ~i; i = tsnxt[i])//遍历TKC所有时态边,收集TCC的时间戳集
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
	for (int i = 0; i < VMAX; ++i)//把每个TCC中的节点ID和时间戳升序排序,用于找到最小的节点编号和最小最大时间戳
	{
		if (ccv_set[i].size())
		{
			sort(ccv_set[i].begin(), ccv_set[i].end());
			sort(cct_set[i].begin(), cct_set[i].end());
		}
	}
	for (auto edge_freq : Mc)//再次遍历所有connection,计算cce_cnt
	{
		//遍历TKC的所有connection,把所在的TCC的connection数量增加1
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		int r = find(u);
		cce_cnt[r] ++;
	}
}

void compute_tcc_prop_set_c(int ts, int te, int k)//获取某个TKC对应TCC的三个Property Set, 输入为TKC参数
{
	//下面三行初始化TKC的TEL和三个辅助结构
	buildtel(ts, te);
	initMH(ts, te);
	decomp(k);

	//下面代码块获取TKC的各个TCC,保存到三个TCC Property Set
	//(u,v)代表一个connection的两个端点,r代表处理的点或边所在的TCC编号(即并查集代表元)

	init_p();//初始化并查集
	for (auto edge_freq : Mc)//遍历TKC所有connection,构建tkc连通性的并查集
	{
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		combine(u, v);
	}
	for (auto vertex_deg : Mv)//遍历TKC所有结点,收集所有TCC的节点集
	{
		int v = vertex_deg.first;
		int r = find(v);
		ccv_set[r].push_back(v);
	}
	for (int i = head; ~i; i = tsnxt[i])//遍历TKC所有时态边,收集TCC的时间戳集合时序边集
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
	for (int i = 0; i < VMAX; ++i)//把每个TCC中的节点ID和时间戳升序排序,用于找到最小的节点编号和最小最大时间戳
	{
		if (ccv_set[i].size())
		{
			sort(ccv_set[i].begin(), ccv_set[i].end());
			sort(cct_set[i].begin(), cct_set[i].end());
		}
	}
	for (auto edge_freq : Mc)//再次遍历所有connection,计算cce_cnt
	{
		//遍历TKC的所有connection,把所在的TCC的connection数量增加1
		int u = edge_freq.first.first;
		int v = edge_freq.first.second;
		int r = find(u);
		cce_cnt[r] ++;
	}
}

template<typename T>
struct OPT_TCC_FOUND {
	/*** 下面三个属性唯一确定一个TCC ***/
	int TTI_TS;//TCC内的最小时间戳
	int TTI_TE;//TCC内的最大时间戳
	int MIN_VERTEX;//TCC内的节点id的最小值

	/*** LS中当前最优TCC的X值 ***/
	T x_value;
};

void LS_BURST(int k)//X=BURSTINESS的LocalSearch,函数输入为time zone的集合(zone_set),k为TXCQ参数，返回BURSTINESS最大的TCC(用三元组表示)
{
	OPT_TCC_FOUND<double> opt_tcc_burst = {-1, -1, -1, 0.0};//用于记录LS过程中BURSTINESS最大的TCC
	for (auto tz : zone_set)//调用前zone_set必须已经通过ZPar_O初始化
	{
		init_tcc_prop_set();//准被获取一个新TKC的所有TCC,先清空对应结果集

		compute_tcc_prop_set(tz, k);//计算TKC的TCC，保存到三个Property Set

		for (int i = 0; i < VMAX; ++i)
		{
			if (ccv_set[i].size())
			{
				//获取到这个TCC的标记三元组
				int TTI_TS = *cct_set[i].begin();
				int TTI_TE = *(--cct_set[i].end());
				int MIN_VERTEX = *ccv_set[i].begin();
				int span_day = (consecutive_timestamp[TTI_TE - 1] - consecutive_timestamp[TTI_TS - 1]) / 86400 + 1;//对于-day数据集，span为天数
				double tcc_burstiness = (double)cce_cnt[i] * 2.0 / (double)span_day;//计算TCC的burstiness,注意分母需要加1,因为TTI_TS可能和TTI_TE相同
				//double tcc_burstiness = (double)ccv_set[i].size() / (double)((double)TTI_TE - TTI_TS + 1.0);
				//printf("burstiness [%d, %d, %d], %.2lf\n", TTI_TS, TTI_TE, MIN_VERTEX, tcc_burstiness);

				if (opt_tcc_burst.TTI_TS == -1 || opt_tcc_burst.x_value < tcc_burstiness)//由于是Optimizing Query,且X计算为常数开销,因此不用考虑dominating关系的TCC被多次考虑的问题
				{
					opt_tcc_burst = { TTI_TS, TTI_TE, MIN_VERTEX, tcc_burstiness };
				}

			}
		}
	}

	printf("TCC with maximum burstiness: [%d, %d, %d] \n", opt_tcc_burst.TTI_TS, opt_tcc_burst.TTI_TE, opt_tcc_burst.MIN_VERTEX);
}

struct TCC_SZ {//TCC SIZE的结构体，用于查找SIZE top-k小的TCC
	int ts, te, vid;//element key,uniquely identify a TCC
	int val;
	bool operator<(const TCC_SZ& another) const//对“低优先级”进行定义,返回true代表优先级“低于”
	{
		return val < another.val;//我们对应SIZE要top-K小的,因此这里需要一个大顶堆，即val越小优先级越低
	}
};

void LS_SIZE(int K, int k)//X=SIZE的LocalSearch,函数输入为time zone的集合(zone_set),K为指定参数,获取SIZE最小的K个TCC,k为TXCQ中的k
{
	//priority_queue, 堆顶元素具有最高优先级
	priority_queue<TCC_SZ, vector<TCC_SZ>> heap_for_max_k;
	//维护队中元素的key集合,用于实现去重,因为同一个TCC可能存在与多个Distinct Core,因此每个TCC只处理一次
	set<pair<pair<int, int>, int>> heap_key;
	for (auto tz : zone_set)//调用前zone_set必须已经通过ZPar_O初始化
	{
		auto TTI = tz.first;
		int ts = TTI.first, te = TTI.second;
		for (int i = 0; i < VMAX; ++i) ccv_set[i].clear();//清空ccv_set
		//下面三行初始化tkc的TEL
		buildtel(ts, te);
		initMH(ts, te);
		decomp(k);
		init_p();//初始化并查集
		for (auto edge_freq : Mc)//构建tkc连通性的并查集
		{
			int u = edge_freq.first.first;
			int v = edge_freq.first.second;
			combine(u, v);
		}
		for (auto vertex_deg : Mv)//收集所有TCC的节点集,rv为一个TCC的代表节点编号
		{
			int v = vertex_deg.first;
			int rv = find(v);
			ccv_set[rv].push_back(v);
		}
		for (int i = 0; i < VMAX; ++i)//把每个TCC中的节点标号升序排序,用于找到最小的节点编号
		{
			if (ccv_set[i].size())
			{
				sort(ccv_set[i].begin(), ccv_set[i].end());
			}
		}
		for (int i = head; ~i; i = tsnxt[i])//收集所有TCC的时间戳集,r为一个TCC的代表节点编号
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
				if (heap_key.find({ {tcc_sz.ts, tcc_sz.te}, tcc_sz.vid }) != heap_key.end())//该TCC已经处理过了
				{
					continue;
				}
				heap_key.insert({ {tcc_sz.ts, tcc_sz.te}, tcc_sz.vid });//标记为已处理过
				if (heap_for_max_k.size() < K || (heap_for_max_k.top().val > tcc_sz.val))//如果对不满K个或这个TCC的size小于堆顶,则更新堆
				{
					if (heap_for_max_k.size() == K) heap_for_max_k.pop();//堆已经满K个,移除堆顶
					heap_for_max_k.push(tcc_sz);//入堆
				}
			}
		}
	}
}

void o_tcc_edge_list(int ts, int te, int k, int v, string file_name)
{
	init_tcc_prop_set();//准被获取一个新TKC的所有TCC,先清空对应结果集
	compute_tcc_prop_set_c(ts, te, k);//计算TKC的TCC，保存到三个Property Set
	for (int i = 0; i < VMAX; ++i)
	{
		if (ccv_set[i].size())
		{
			if (ccv_set[i][0] == v)//确认为需要的TCC输出
			{
				ofstream ofile(file_name.c_str());
				ofile << "Source" << "," << "Target" << "," << "Timestamp" << "\n";
				for (int eid : cce_set[i])
				{
					ofile << arcs[eid].src << ',' << arcs[eid].dst << ',' << arcs[eid].t << '\n';
				}
				break;//指定的TCC是唯一的,输出后直接break
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
	unordered_map<pair<int, int>, int, pair_hash> conn_stre;//保存[ts,te]下各条connection的strength
	for (int i = 0; i < arcn; ++i)//初始化[ts,te]下各条connection的strength
		if (arcs[i].t >= ts && arcs[i].t <= te)
		{
			if (conn_stre.find({ arcs[i].src, arcs[i].dst }) == conn_stre.end())
			{
				conn_stre[{arcs[i].src, arcs[i].dst}] = 0;
			}
			conn_stre[{arcs[i].src, arcs[i].dst}] ++;
		}
	vector<int> edge_list;
	for(int i = 0; i < arcn; ++ i)//获取[ts,te]下connection strength不小于h的所有connection包含的时态边集
		if (arcs[i].t >= ts && arcs[i].t <= te)
			if (conn_stre[{arcs[i].src, arcs[i].dst}] >= h)
			{
				edge_list.push_back(i);
			}
	//利用edge_list初始化[ts,te]下(k,h)-core的TEL,Mc,Mv,Hv
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