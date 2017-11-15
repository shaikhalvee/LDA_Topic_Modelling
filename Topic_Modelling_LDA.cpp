/*-------property of the half blood prince-----*/

#include <bits/stdc++.h>
#include <dirent.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#include <ext/pb_ds/detail/standard_policies.hpp>
#define MIN(X,Y) X<Y?X:Y
#define MAX(X,Y) X>Y?X:Y
#define ISNUM(a) ('0'<=(a) && (a)<='9')
#define ISCAP(a) ('A'<=(a) && (a)<='Z')
#define ISSML(a) ('a'<=(a) && (a)<='z')
#define ISALP(a) (ISCAP(a) || ISSML(a))
#define MXX 10000000000
#define MNN -MXX
#define ISVALID(X,Y,N,M) ((X)>=1 && (X)<=(N) && (Y)>=1 && (Y)<=(M))
#define LLI long long int
#define VI vector<int>
#define VLLI vector<long long int>
#define VS vector<string>
#define MII map<int,int>
#define SI set<int>
#define PB push_back
#define MSI map<string,int>
#define PII pair<int,int>
#define PLLI pair<LLI,LLI>
#define FREP(i,I,N) for(int (i)=(int)(I);(i)<=(int)(N);(i)++)
#define eps 0.0000000001
#define RFREP(i,N,I) for(int (i)=(int)(N);(i)>=(int)(I);(i)--)
#define SORTV(VEC) sort(VEC.begin(),VEC.end())
#define SORTVCMP(VEC,cmp) sort(VEC.begin(),VEC.end(),cmp)
#define REVV(VEC) reverse(VEC.begin(),VEC.end())
using namespace std;
using namespace __gnu_pbds;

//int dx[]={1,0,-1,0};int dy[]={0,1,0,-1}; //4 Direction
//int dx[]={1,1,0,-1,-1,-1,0,1};int dy[]={0,1,1,1,0,-1,-1,-1};//8 direction
//int dx[]={2,1,-1,-2,-2,-1,1,2};int dy[]={1,2,2,1,-1,-2,-2,-1};//Knight Direction
//int dx[]={2,1,-1,-2,-1,1};int dy[]={0,1,1,0,-1,-1}; //Hexagonal Direction


typedef tree < int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update > ordered_set;

string dir="20newsgroups";
char *dirname;
int topic_number=10;
int seeddone=0;
int NITER=5000;
int freqword=10;
int init_burn_in=2000;
int lag_percentage=20;
int burn_flag=0;
int lag_flag=1;

double alpha,beta;

vector<VI>final_ntv;
VS filenames;
VI docsize; VI cumulative_doc_size; VI Z;
VS Words; set<string>Vocab; map<string,int>vocab_numerate;
vector<string>vocabvector;
vector<VI>topic_wcnt_doc; //ntd
vector<VI>word_tcnt; //ntv
VI summation_word_tcnt; //one entry for each topic
VI summation_topic_wcnt_doc; //one entry for each doc
vector<double>topic_prob;

void print(vector<string>v){FREP(i,0,v.size()-1)cout<<v[i]<<" ";cout<<"\n";}
void print(vector<int>v){FREP(i,0,v.size()-1)cout<<v[i]<<" ";cout<<"\n";}
void print(vector<double>v){FREP(i,0,v.size()-1)cout<<v[i]<<" ";cout<<"\n";}

void normalizep(){
    double s=0.0;
    FREP(i,0,topic_prob.size()-1){
        s=s+topic_prob[i];
    }
    FREP(i,0,topic_prob.size()-1){
        topic_prob[i]/=s;
    }
    FREP(i,1,topic_prob.size()-1){
        topic_prob[i]=topic_prob[i]+topic_prob[i-1];
    }
}

int samplenewtopic(){
    if(!seeddone){
        srand(time(0));
        seeddone=1;
    }
    double r = (double)rand()/(double)RAND_MAX;
    FREP(i,0,topic_prob.size()-1){
        if(r<topic_prob[i] || fabs(r-topic_prob[i])<eps)return i;
    }
    return -1;
}

void sethyperparameter(){
    alpha=50.0/(double)topic_number;
    beta=0.1;
}

void initz(){ //initialize Z array with totally random topics
    if(!seeddone){
        srand(time(0));
        seeddone=1;
    }
    FREP(i,0,Words.size()-1){
        int t=rand()%topic_number;
        Z.PB(t);
    }
}

void enum_vocab(){ //enumerate words in a vocabulary, each word appears only once
    set<string>::iterator it;
    int idx=0;
    for(it=Vocab.begin();it!=Vocab.end();++it){vocab_numerate[*it]=idx++;vocabvector.PB(*it);}
}

void init_helper_matrices(){ //init ntv,ntd,array of probabilities
    FREP(i,0,docsize.size()-1){
        VI line;
        topic_wcnt_doc.PB(line);
        summation_topic_wcnt_doc.PB(0);
        FREP(j,0,topic_number-1) topic_wcnt_doc[i].PB(0);
    }
    FREP(i,0,topic_number-1){
        VI line;
        word_tcnt.PB(line);
        final_ntv.PB(line);
        summation_word_tcnt.PB(0);
        FREP(j,0,Vocab.size()-1) {word_tcnt[i].PB(0); final_ntv[i].PB(0);}
    }
    FREP(i,0,topic_number-1) topic_prob.PB(0.0);
}

void clear_helper_matrices(){ //resets ntv, ntd , prob array but keep the sizes
    FREP(i,0,docsize.size()-1) FREP(j,0,topic_number-1) topic_wcnt_doc[i][j]=0;
    FREP(i,0,topic_number-1) FREP(j,0,Vocab.size()-1) word_tcnt[i][j]=0;
    FREP(i,0,topic_number-1) topic_prob[i]=0.0;
}

void arrange_n_t_doc(){ //populates ntd according to Z array
    int didx=0;
    int nxtstop=cumulative_doc_size[didx+1]-1;
    FREP(i,0,Words.size()-1){
        int cur_topic=Z[i];
        topic_wcnt_doc[didx][cur_topic]++;
        summation_topic_wcnt_doc[didx]++;
        if(i==nxtstop){
            didx++;
            if(didx<(int)docsize.size())nxtstop=cumulative_doc_size[didx+1]-1;
        }
    }
}

void arrange_n_t_vocab(){ //populates ntv according to Z array
    FREP(i,0,Words.size()-1){
        int cur_topic=Z[i];
        int cur_word=vocab_numerate[Words[i]];
        word_tcnt[cur_topic][cur_word]++;
        summation_word_tcnt[cur_topic]++;
    }
}

void populate_final_ntv(){
    FREP(i,0,Words.size()-1){
        int cur_topic=Z[i];
        int cur_word=vocab_numerate[Words[i]];
        final_ntv[cur_topic][cur_word]++;
    }
}

vector<string>getwords(int docidx){ //given a docnumber (1 based) returns its words
    vector<string>dw;
    int start=cumulative_doc_size[docidx-1]; int ed=cumulative_doc_size[docidx]-1;
    FREP(i,start,ed)dw.PB(Words[i]);
    return dw;
}

void storeword(ifstream &fin){ //stores words from one file
    string w;
    int cnt=0;
    while(fin>>w){
        cnt++;
        Words.PB(w);Vocab.insert(w);
    }
    docsize.PB(cnt);
}

void iteratefolder(char *dir){ //stores all filenames of a folder
    struct dirent *pDirent;
    DIR *pDir;
    pDir = opendir (dir);
    if (pDir == NULL) {
        printf ("Cannot open directory '%s'\n", dir);
        return;
    }
    while ((pDirent = readdir(pDir)) != NULL) {
        if(ISNUM(pDirent->d_name[0]) || ISALP(pDirent->d_name[0])){
            string fname(pDirent->d_name);
            filenames.PB(fname);
        }
    }
    closedir(pDir);
}

void iteratefiles(){ //iterates all files from filenames
    int tot=filenames.size();
    FREP(i,0,(tot-1)){
        string location=dir+"/"+filenames[i];
        ifstream fin(location);
        storeword(fin);
        fin.close();
    }
    cumulative_doc_size.PB(0);
    FREP(i,0,docsize.size()-1) cumulative_doc_size.PB(cumulative_doc_size[i]+docsize[i]);
    enum_vocab();
}

void initdirname(string dir){ //converts string dir to a char array
    dirname=new char[dir.size()+1];
    FREP(i,0,dir.size()-1) dirname[i]=dir[i];
    dirname[dir.size()]='\0';
}

int finddoc(int w){ //given index of Words find which doc it belongs to 1 based
    int lo=0;
    int hi=cumulative_doc_size.size()-1;
    while(true){
        int mid=(lo+hi)/2;
        if(cumulative_doc_size[mid]>w){
            if(mid==0 || cumulative_doc_size[mid-1]<=w){
                return mid;
            }
            else{
                hi=mid;
            }
        }
        else{
            lo=mid+1;
        }
    }
}

void samplez(int i){ //given an instance of z resamples it
    string wi=Words[i];
    int v=vocab_numerate[wi];
    int d=finddoc(i)-1; //jehetu finddoc 1 based dey
    //cout<<"current doc "<<d<<"\n";
    //cout<<"current word: "<<wi<<" word in vocab: "<<v<<"\n";
    int t=Z[i];
    int V=Vocab.size();
    topic_wcnt_doc[d][t]=topic_wcnt_doc[d][t]-1; summation_topic_wcnt_doc[d]--;
    word_tcnt[t][v]=word_tcnt[t][v]-1; summation_word_tcnt[t]--;
    FREP(topicidx,0,topic_number-1){
        //cout<<"at topicidx "<<topicidx<<"\n";
        //cout<<topic_wcnt_doc[d][topicidx]<<" "<<summation_topic_wcnt_doc[d]<<"\n";
        //cout<<word_tcnt[topicidx][v]<<" "<<summation_word_tcnt[topicidx]<<"\n";
        double lob1=alpha+topic_wcnt_doc[d][topicidx];
        double hor1=(topic_number)*alpha+summation_topic_wcnt_doc[d];
        double lob2=beta+word_tcnt[topicidx][v];
        double hor2=V*beta+summation_word_tcnt[topicidx];
        topic_prob[topicidx]=(lob1*lob2)/(hor1*hor2);
        //if(topic_prob[topicidx]>=0.0)cout<<"minus ashe na\n";
    }
    normalizep();
    //print(topic_prob);
    int nt=samplenewtopic();
    // cout<<"new topic "<<nt<<"\n";
    Z[i]=nt;
    topic_wcnt_doc[d][nt]=topic_wcnt_doc[d][nt]+1; summation_topic_wcnt_doc[d]++;
    word_tcnt[nt][v]=word_tcnt[nt][v]+1; summation_word_tcnt[nt]++;
}

void gibbs( int niter){
    initz();
    int burninval=init_burn_in*burn_flag;
    int dif=lag_flag?((lag_percentage*(niter-burninval))/(100)):1;
    cout<<dif<<"\n";
    sethyperparameter();
    init_helper_matrices();
    arrange_n_t_doc();
    arrange_n_t_vocab();
    int nextiter=-1;
    FREP(i,1,niter){
        cout<<"iteration "<<i<<"\n";
        FREP(idx,0,Words.size()-1){
            samplez(idx);
        }
        if(burninval>0)burninval--;
        //cout<<"hoise\n";
        if(burninval==0 && nextiter==-1){
            nextiter=i;
        }
        if(burninval==0){
            if(i==nextiter){
                cout<<"saving at "<<nextiter<<"\n";
                populate_final_ntv();
                nextiter+=dif;
            }
        }
    }
}

void printfreqwords(int topicidx, int numwords){
    vector<PII>cnt;
    int V=Vocab.size();
    FREP(i,0,(V-1)){
        cnt.PB(make_pair(-final_ntv[topicidx][i],i));
    }
    SORTV(cnt);
    cout<<numwords<<" most freq words for topic "<<topicidx<<": ";
    FREP(i,0,min(numwords-1,(int)cnt.size()-1)){
        //cout<<-cnt[i].first<<" ";
        int wordidx=cnt[i].second;
        cout<<vocabvector[wordidx]<<" ";
    }
    cout<<"\n";
}

int main(){
    initdirname(dir);
    iteratefolder(dirname);
    iteratefiles();
    //print(Words);
    //print(docsize);
    //print(cumulative_doc_size);
    gibbs(NITER);
    cout<<"Ran with Niter: "<<NITER<<" burn-in: "<<burn_flag*init_burn_in<<" lag: "<<lag_percentage*lag_flag<<"\n";
    FREP(i,0,topic_number-1){
        printfreqwords(i,freqword);
    }
    return 0;
}
