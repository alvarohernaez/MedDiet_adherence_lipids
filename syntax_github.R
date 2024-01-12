rm(list=ls())

library(chron)
library(colorspace)
library(mime)
library(dichromat)
library(munsell)
library(labeling)
library(rlang)
library(stringi)
library(evaluate)
library(highr)
library(markdown)
library(yaml)
library(backports)
library(jsonlite)
library(digest)
library(plyr)
library(reshape2)
library(scales)
library(tibble)
library(lazyeval)
library(RColorBrewer)
library(stringr)
library(knitr)
library(magrittr)
library(checkmate)
library(htmlwidgets)
library(viridisLite)
library(Rcpp)
library(Formula)
library(ggplot2)
library(latticeExtra)
library(acepack)
library(gtable)
library(gridExtra)
library(data.table)
library(htmlTable)
library(viridis)
library(htmltools)
library(base64enc)
library(minqa)
library(RcppEigen)
library(lme4)
library(SparseM)
library(MatrixModels)
library(pbkrtest)
library(quantreg)
library(car)
library(htmlTable)
library(Hmisc)
library(survival)
library(foreign)
library(bitops)
library(caTools)
library(gplots)
library(ROCR)
library(RODBC)
library(compareGroups)
library(nlme)
library(vcd)
library(psy)
library(irr)
library(boot)
library(tibble)
library(haven)
library(icenReg)
library(arm)
library(standardize)
library(MASS)
library(sandwich)   
library(lmtest)
library(gam)
library(smoothHR)
library(meta)
library(metafor)
library(mgcv)
library(gratia)
library(MuMIn)
library(plotrix)
library(tidyr)
library(nephro)


### GUAPAS ###
##############

guapa<-function(x)
{
  redondeo<-ifelse(abs(x)<0.00001,signif(x,1),
                   ifelse(abs(x)<0.0001,signif(x,1),
                          ifelse(abs(x)<0.001,signif(x,1),
                                 ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                        ifelse(abs(x)<1,sprintf("%.2f",round(x,2)),
                                               ifelse(abs(x)<10,sprintf("%.2f",round(x,2)),
                                                      ifelse(abs(x)<100,sprintf("%.1f",round(x,1)),
                                                             ifelse(abs(x)>=100,round(x,0),round(x,0)))))))))
  return(redondeo)
}

ic_guapa<-function(x,y,z)
{
  ic<-paste(x," [",y,"; ",z,"]",sep="")
  return(ic)
}

ic_guapa2<-function(x,y,z)
{
  ic<-paste(x," (",y," to ",z,")",sep="")
  return(ic)
}

pval_guapa<-function(x)
{
  pval<-ifelse(x<0.00001,"<0.00001",
               ifelse(x<0.001,"<0.001",
                      ifelse(abs(x)<0.01,sprintf("%.3f",round(x,3)),
                             ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                    ifelse(abs(x)<1,sprintf("%.3f",round(x,3)),guapa(x))))))
  return(pval)
}

pval_guapa2<-function(x)
{
  pval<-ifelse(x<0.00001," < 0.00001",
               ifelse(x<0.001," < 0.001",
                      ifelse(abs(x)<0.01,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                             ifelse(abs(x)<0.1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                                    ifelse(abs(x)<1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),guapa(x))))))
  return(pval)
}

mean_ic_guapa <- function(x, na.rm=FALSE) 
{
  if (na.rm) x <- na.omit(x)
  se<-sqrt(var(x)/length(x))
  z<-qnorm(1-0.05/2)
  media<-mean(x)
  ic95a<-guapa(media-(z*se))
  ic95b<-guapa(media+(z*se))
  media<-guapa(media)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

mean_sd_guapa <- function(x) 
{
  media<-guapa(mean(x, na.rm=TRUE))
  sd<-guapa(sd(x, na.rm=TRUE))
  end<-paste(media," (",sd,")",sep="")
  return(end)
}

beta_se_ic_guapa <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

beta_se_ic_guapa2 <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa2(media,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa2 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa3 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-round(exp(x),3)
  ic95a<-round(exp(x-(z*y)),3)
  ic95b<-round(exp(x+(z*y)),3)
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

header.true <- function(df)
{
  names(df) <- as.character(unlist(df[1,]))
  df[-1,]
}

z<-qnorm(1-0.05/2)

closest<-function(xv,sv){
  xv[which(abs(xv-sv)==min(abs(xv-sv)))] }

# Suppress scientific notation for coefficients (no "4e-04", instead "0.0004")
options(scipen=999)

setwd("C:/.../lipids")


################
### ANALYSES ###
################

##########################
### DESCRIPTIVE TABLES ###
##########################

load("./Results/Data/predimed_lipids.RData")

xxx<-dat[,c("id","edad","sexo","escolar00",
            "dmed00","dmed00_cat2","dmed00_cat4","dmed_long","dmed_long_cat2","dmed_long_cat4",
            "diabetes00","hipercolest00","col00","ldl00","hdl00","f_col00","hipertg00","tg00","f_tg00",
            "nonhdl00","hta00","tabaco00","obesidad00","af00","kcal00")]
xxx$sel<-1


long2<-NULL
long2<-createTable(compareGroups(dmed_long_cat2~.
                                 -id-sel-dmed00_cat4-dmed00_cat2-dmed_long_cat4,
                                 xxx, method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercolest00"=3,
                                               "f_col00"=3,"hipertg00"=3,"f_tg00"=3,
                                               "hta00"=3,"tabaco00"=3,"obesidad00"=3,
                                               "af00"=2,"tg00"=2)),
                   show.n=TRUE, hide.no=0)

tab2<-NULL
tab2<-createTable(compareGroups(sel~.
                                -id-dmed00_cat2-dmed00_cat4-dmed_long_cat2-dmed_long_cat4,
                                xxx, method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercolest00"=3,
                                              "f_col00"=3,"hipertg00"=3,"f_tg00"=3,
                                              "hta00"=3,"tabaco00"=3,"obesidad00"=3,
                                              "af00"=2,"tg00"=2)),
                  show.n=TRUE, hide.no=0)

long2<-cbind(tab2$descr[,1],long2$descr)
colnames(long2)<-c("All","<10",">=10","P-value","N")
write.table(long2,file="./Results/Outputs/Descriptive/desc_long2.csv",sep=";",col.names=NA)


############################################################################
### NUMBER OF PARTICIPANTS WITH LIPID PROFILE VALUES IN THE STUDY VISITS ###
############################################################################

load("./Results/Data/predimed_lipids.RData")

vars01<-c("tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07")
vars02<-c("hdl00","hdl01","hdl02","hdl03","hdl04","hdl05","hdl06","hdl07")
vars03<-c("ldl00","ldl01","ldl02","ldl03","ldl04","ldl05","ldl06","ldl07")

tab<-NULL
for(i in 1:length(vars01))
  
{
  det1<-length(which(!is.na(dat[,vars01[i]])))
  det2<-length(which(!is.na(dat[,vars02[i]])))
  det3<-length(which(!is.na(dat[,vars03[i]])))
  tab<-rbind(tab,cbind(det1,det2,det3))
}

tab<-t(tab)
rownames(tab)<-c("Triglycerides","HDL-C","LDL-C")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years")
write.table(tab,file="./Results/Outputs/Descriptive/rep_measures_values.csv",sep=";",col.names=NA)


############################################################################
### TRAJECTORY ANALYSES: MIXED LINEAR MODELS WITH SMOOTHED CUBIC SPLINES ###
############################################################################

z<-qnorm(1-0.05/2)
se <- function(x) sqrt(var(x) / length(x))

vars00<-c("LDL cholesterol, mg/dL\n(predicted values, 95% CI)",
          "HDL cholesterol, mg/dL\n(predicted values, 95% CI)",
          "Triglycerides, mg/dL\n(predicted values, 95% CI)")
vars01<-c("ldl","hdl","tg")
vars02<-c("ldl_basal","hdl_basal","tg_basal")
vars03<-c("f_col_basal","f_tg_basal","f_tg_basal")
vars05<-c("ldl_hi160_inicio","hdl_lo_inicio","tg_hi150_inicio")

vars04<-c("0","0.1","0.2","0.3","0.4","0.5","0.6","0.7","0.8","0.9",
          "1","1.1","1.2","1.3","1.4","1.5","1.6","1.7","1.8","1.9",
          "2","2.1","2.2","2.3","2.4","2.5","2.6","2.7","2.8","2.9",
          "3","3.1","3.2","3.3","3.4","3.5","3.6","3.7","3.8","3.9",
          "4","4.1","4.2","4.3","4.4","4.5","4.6","4.7","4.8","4.9","5")

tab<-NULL
tab2<-NULL

for(i in 1:length(vars01))
  
{
  # 2 CATEGORIES - ALL PARTICIPANTS #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  pval_int<-c("NULL")
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,dat_long$grup_int,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  #leg<-paste("Time*group interaction p-value",pval_time_group,
  #           "\nNon-linearity p-value",pval_lrtest,sep="")
  maxx<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                              ifelse(max(group0_hi,na.rm=TRUE)<max(group1_hi,na.rm=TRUE),max(group1_hi,na.rm=TRUE),
                                     ifelse(max(group0_hi,na.rm=TRUE)==max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#D55E00") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#D55E00') +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Results/Outputs/Repeated/",vars01[i],"_cat2.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("<10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  
  # 2 CATEGORIES - SEPARATION BETWEEN CONDITION AT BASELINE #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02",vars05[i])]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02","strat")
  xxx$id2<-as.factor(xxx$id)
  
  mod_gam01<-lme(variable~bs(seg,df=4)*group+strat+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  mod_gam02<-lme(variable~bs(seg,df=4)*group*strat+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  pval_int<-pval_guapa(lrtest(mod_gam01,mod_gam02)[2,5])
  
  # NO CONDITION AT BASELINE #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars05[i]]==0")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,dat_long$grup_int,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data01<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("No condition, <10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  # YES CONDITION AT BASELINE #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars05[i]]==1")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,dat_long$grup_int,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data02<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("Yes condition, <10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  
  plot.data02<-rename.vars(plot.data02,
                           from=c("group0_fit","group0_lo","group0_hi","group1_fit","group1_lo","group1_hi"),
                           to=c("group2_fit","group2_lo","group2_hi","group3_fit","group3_lo","group3_hi"))
  plot.data<-merge2(plot.data01,plot.data02,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  #leg<-paste("Time*group interaction p-value",pval_time_group,
  #           "\nNon-linearity p-value",pval_lrtest,sep="")
  maxx1<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group1_hi,na.rm=TRUE),max(group1_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx2<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group2_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group2_hi,na.rm=TRUE),max(group2_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group2_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx3<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group3_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group3_hi,na.rm=TRUE),max(group3_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group3_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx<-ifelse(maxx1>maxx2,maxx1,
               ifelse(maxx1<maxx2,maxx2,
                      ifelse(maxx1==maxx2,maxx1,NA)))
  maxx<-ifelse(maxx>maxx3,maxx,
               ifelse(maxx<maxx3,maxx3,
                      ifelse(maxx==maxx3,maxx,NA)))
  
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#fc8dc4") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#fc8dc4') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#de026e") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#de026e') +
    geom_ribbon(aes_string(ymin='group2_lo', ymax='group2_hi'), alpha=0.25, fill="#9e88fc") +
    geom_line(aes_string(x='seg', y='group2_fit'), color='#9e88fc') +
    geom_ribbon(aes_string(ymin='group3_lo', ymax='group3_hi'), alpha=0.25, fill="#5833ff") +
    geom_line(aes_string(x='seg', y='group3_fit'), color='#5833ff') +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Results/Outputs/Repeated/",vars01[i],"_cat2_cond_baseline.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  
  # 2 CATEGORIES - SEPARATION BETWEEN TREATMENT AT BASELINE #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_gam01<-lme(variable~bs(seg,df=4)*group+tt+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
                 +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  mod_gam02<-lme(variable~bs(seg,df=4)*group*tt+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
                 +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  pval_int<-pval_guapa(lrtest(mod_gam01,mod_gam02)[2,5])
  
  # NO TREATMENT AT BASELINE #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars03[i]]==0")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal","hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,dat_long$grup_int,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data01<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("No treatment, <10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  # YES CONDITION AT BASELINE #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars03[i]]==1")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int",
                   "diabetes00","col_basal","hdl_basal","tg_basal","hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,dat_long$grup_int,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data02<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("Yes treatment, <10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  
  plot.data02<-rename.vars(plot.data02,
                           from=c("group0_fit","group0_lo","group0_hi","group1_fit","group1_lo","group1_hi"),
                           to=c("group2_fit","group2_lo","group2_hi","group3_fit","group3_lo","group3_hi"))
  plot.data<-merge2(plot.data01,plot.data02,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  #leg<-paste("Time*group interaction p-value",pval_time_group,
  #           "\nNon-linearity p-value",pval_lrtest,sep="")
  maxx1<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group1_hi,na.rm=TRUE),max(group1_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx2<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group2_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group2_hi,na.rm=TRUE),max(group2_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group2_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx3<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group3_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group3_hi,na.rm=TRUE),max(group3_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group3_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx<-ifelse(maxx1>maxx2,maxx1,
               ifelse(maxx1<maxx2,maxx2,
                      ifelse(maxx1==maxx2,maxx1,NA)))
  maxx<-ifelse(maxx>maxx3,maxx,
               ifelse(maxx<maxx3,maxx3,
                      ifelse(maxx==maxx3,maxx,NA)))
  
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#44AA99") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#44AA99') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#117733") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#117733') +
    geom_ribbon(aes_string(ymin='group2_lo', ymax='group2_hi'), alpha=0.25, fill="#CC6677") +
    geom_line(aes_string(x='seg', y='group2_fit'), color='#CC6677') +
    geom_ribbon(aes_string(ymin='group3_lo', ymax='group3_hi'), alpha=0.25, fill="#882255") +
    geom_line(aes_string(x='seg', y='group3_fit'), color='#882255') +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Results/Outputs/Repeated/",vars01[i],"_cat2_tt_baseline.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  
  # 2 CATEGORIES - SEPARATION BETWEEN PREDIMED INTERVENTION GROUP #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_gam01<-lme(variable~bs(seg,df=4)*group+grup_int+edad+sexo+as.factor(nodo)+as.factor(escolar)
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  mod_gam02<-lme(variable~bs(seg,df=4)*group*grup_int+edad+sexo+as.factor(nodo)+as.factor(escolar)
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  pval_int<-pval_guapa(lrtest(mod_gam01,mod_gam02)[2,5])
  
  # MEDDIET INTERVENTION GROUPS #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long$grup_int2==1")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data01<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("MedDiet groups, <10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  # CONTROL ARM #
  
  load("./Results/Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long$grup_int2==0")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","segyears","edad","sexo","nodo","escolar00",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco00",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","edad","sexo","nodo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  
  mod_lin<-lme(variable~seg*group+edad+sexo+as.factor(nodo)+as.factor(escolar)
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+edad+sexo+as.factor(nodo)+as.factor(escolar)
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+edad+sexo+as.factor(nodo)+as.factor(escolar)
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(0,5,by=0.10),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$edad,dat_long$sexo,dat_long$nodo,dat_long$escolar00,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco00,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","edad","sexo","nodo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group<-as.numeric(gam_predict$group)-1
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict$escolar<-as.factor(gam_predict$escolar)
  gam_predict$nodo<-as.factor(gam_predict$nodo)
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data02<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==0 | gam_predict$seg==1 | gam_predict$seg==2 | gam_predict$seg==3 | gam_predict$seg==4 | gam_predict$seg==5,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v0","v1","v2","v3","v4","v5")
  
  mod00<-lm(v0~as.factor(group),data=gam_predictx)
  mod01<-lm(v1~as.factor(group),data=gam_predictx)
  mod02<-lm(v2~as.factor(group),data=gam_predictx)
  mod03<-lm(v3~as.factor(group),data=gam_predictx)
  mod04<-lm(v4~as.factor(group),data=gam_predictx)
  mod05<-lm(v5~as.factor(group),data=gam_predictx)
  
  class_g1<-c("Control arm, <10 vs. >=10")
  
  beta00_g1<-intervals(mod00)[2,1]
  lo00_g1<-intervals(mod00)[2,2]
  hi00_g1<-intervals(mod00)[2,3]
  coef00_g1<-ic_guapa2(guapa(beta00_g1),guapa(lo00_g1),guapa(hi00_g1))
  pval00_g1<-pval_guapa(intervals(mod00)[2,4])
  beta01_g1<-intervals(mod01)[2,1]
  lo01_g1<-intervals(mod01)[2,2]
  hi01_g1<-intervals(mod01)[2,3]
  coef01_g1<-ic_guapa2(guapa(beta01_g1),guapa(lo01_g1),guapa(hi01_g1))
  pval01_g1<-pval_guapa(intervals(mod01)[2,4])
  beta02_g1<-intervals(mod02)[2,1]
  lo02_g1<-intervals(mod02)[2,2]
  hi02_g1<-intervals(mod02)[2,3]
  coef02_g1<-ic_guapa2(guapa(beta02_g1),guapa(lo02_g1),guapa(hi02_g1))
  pval02_g1<-pval_guapa(intervals(mod02)[2,4])
  beta03_g1<-intervals(mod03)[2,1]
  lo03_g1<-intervals(mod03)[2,2]
  hi03_g1<-intervals(mod03)[2,3]
  coef03_g1<-ic_guapa2(guapa(beta03_g1),guapa(lo03_g1),guapa(hi03_g1))
  pval03_g1<-pval_guapa(intervals(mod03)[2,4])
  beta04_g1<-intervals(mod04)[2,1]
  lo04_g1<-intervals(mod04)[2,2]
  hi04_g1<-intervals(mod04)[2,3]
  coef04_g1<-ic_guapa2(guapa(beta04_g1),guapa(lo04_g1),guapa(hi04_g1))
  pval04_g1<-pval_guapa(intervals(mod04)[2,4])
  beta05_g1<-intervals(mod05)[2,1]
  lo05_g1<-intervals(mod05)[2,2]
  hi05_g1<-intervals(mod05)[2,3]
  coef05_g1<-ic_guapa2(guapa(beta05_g1),guapa(lo05_g1),guapa(hi05_g1))
  pval05_g1<-pval_guapa(intervals(mod05)[2,4])
  
  tab<-rbind(tab,cbind(class_g1,beta00_g1,lo00_g1,hi00_g1,beta01_g1,lo01_g1,hi01_g1,beta02_g1,lo02_g1,hi02_g1,
                       beta03_g1,lo03_g1,hi03_g1,beta04_g1,lo04_g1,hi04_g1,beta05_g1,lo05_g1,hi05_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef00_g1,pval00_g1,coef01_g1,pval01_g1,coef02_g1,pval02_g1,
                         coef03_g1,pval03_g1,coef04_g1,pval04_g1,coef05_g1,pval05_g1))
  
  
  plot.data02<-rename.vars(plot.data02,
                           from=c("group0_fit","group0_lo","group0_hi","group1_fit","group1_lo","group1_hi"),
                           to=c("group2_fit","group2_lo","group2_hi","group3_fit","group3_lo","group3_hi"))
  plot.data<-merge2(plot.data01,plot.data02,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  #leg<-paste("Time*group interaction p-value",pval_time_group,
  #           "\nNon-linearity p-value",pval_lrtest,sep="")
  maxx1<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group1_hi,na.rm=TRUE),max(group1_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group1_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx2<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group2_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group2_hi,na.rm=TRUE),max(group2_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group2_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx3<-with(plot.data,ifelse(max(group0_hi,na.rm=TRUE)>max(group3_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),
                               ifelse(max(group0_hi,na.rm=TRUE)<max(group3_hi,na.rm=TRUE),max(group3_hi,na.rm=TRUE),
                                      ifelse(max(group0_hi,na.rm=TRUE)==max(group3_hi,na.rm=TRUE),max(group0_hi,na.rm=TRUE),NA))))
  maxx<-ifelse(maxx1>maxx2,maxx1,
               ifelse(maxx1<maxx2,maxx2,
                      ifelse(maxx1==maxx2,maxx1,NA)))
  maxx<-ifelse(maxx>maxx3,maxx,
               ifelse(maxx<maxx3,maxx3,
                      ifelse(maxx==maxx3,maxx,NA)))
  
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#F6624B") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#F6624B') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#B31529") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#B31529') +
    geom_ribbon(aes_string(ymin='group2_lo', ymax='group2_hi'), alpha=0.25, fill="#3A93C3") +
    geom_line(aes_string(x='seg', y='group2_fit'), color='#3A93C3') +
    geom_ribbon(aes_string(ymin='group3_lo', ymax='group3_hi'), alpha=0.25, fill="#1065B1") +
    geom_line(aes_string(x='seg', y='group3_fit'), color='#1065B1') +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Results/Outputs/Repeated/",vars01[i],"_cat2_interv_group.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
}

rownames(tab)<-c("LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)",
                 "LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)",
                 "HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)",
                 "HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)",
                 "triglycerides (mg/dL)","triglycerides (mg/dL)",
                 "triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)"
rownames(tab2)<-c("LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C",
                  "HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C",
                  "TG","TG","TG","TG","TG","TG","TG")
write.table(tab,file="./Results/Outputs/Repeated/forestplots.csv",sep=";",col.names=NA)
write.table(tab2,file="./Results/Outputs/Repeated/repeated.csv",sep=";",col.names=NA)


######################################################
### FOREST PLOTS OF DIFFERENCES IN PREDICTED MEANS ###
######################################################

dat<-read.csv2("./Results/Outputs/Repeated/forestplots.csv",header=TRUE,sep=";",dec=".")

vars01<-c(4,14,24)
vars02<-c(10,20,30)
vars03<-c("ldl","hdl","tg")

for(i in 1:length(vars01))
  
{
  tabx<-dat[vars01[i]:vars02[i],]
  tab<-NULL
  tab<-rbind(cbind(c(0,0,0,0,0,0,0),
                   rbind(tab,cbind(tabx$beta00_g1[1],tabx$lo00_g1[1],tabx$hi00_g1[1]),
                         cbind(tabx$beta00_g1[2],tabx$lo00_g1[2],tabx$hi00_g1[2]),
                         cbind(tabx$beta00_g1[3],tabx$lo00_g1[3],tabx$hi00_g1[3]),
                         cbind(tabx$beta00_g1[4],tabx$lo00_g1[4],tabx$hi00_g1[4]),
                         cbind(tabx$beta00_g1[5],tabx$lo00_g1[5],tabx$hi00_g1[5]),
                         cbind(tabx$beta00_g1[6],tabx$lo00_g1[6],tabx$hi00_g1[6]),
                         cbind(tabx$beta00_g1[7],tabx$lo00_g1[7],tabx$hi00_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(1,1,1,1,1,1,1),
                   rbind(tab,cbind(tabx$beta01_g1[1],tabx$lo01_g1[1],tabx$hi01_g1[1]),
                         cbind(tabx$beta01_g1[2],tabx$lo01_g1[2],tabx$hi01_g1[2]),
                         cbind(tabx$beta01_g1[3],tabx$lo01_g1[3],tabx$hi01_g1[3]),
                         cbind(tabx$beta01_g1[4],tabx$lo01_g1[4],tabx$hi01_g1[4]),
                         cbind(tabx$beta01_g1[5],tabx$lo01_g1[5],tabx$hi01_g1[5]),
                         cbind(tabx$beta01_g1[6],tabx$lo01_g1[6],tabx$hi01_g1[6]),
                         cbind(tabx$beta01_g1[7],tabx$lo01_g1[7],tabx$hi01_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(2,2,2,2,2,2,2),
                   rbind(tab,cbind(tabx$beta02_g1[1],tabx$lo02_g1[1],tabx$hi02_g1[1]),
                         cbind(tabx$beta02_g1[2],tabx$lo02_g1[2],tabx$hi02_g1[2]),
                         cbind(tabx$beta02_g1[3],tabx$lo02_g1[3],tabx$hi02_g1[3]),
                         cbind(tabx$beta02_g1[4],tabx$lo02_g1[4],tabx$hi02_g1[4]),
                         cbind(tabx$beta02_g1[5],tabx$lo02_g1[5],tabx$hi02_g1[5]),
                         cbind(tabx$beta02_g1[6],tabx$lo02_g1[6],tabx$hi02_g1[6]),
                         cbind(tabx$beta02_g1[7],tabx$lo02_g1[7],tabx$hi02_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(3,3,3,3,3,3,3),
                   rbind(tab,cbind(tabx$beta03_g1[1],tabx$lo03_g1[1],tabx$hi03_g1[1]),
                         cbind(tabx$beta03_g1[2],tabx$lo03_g1[2],tabx$hi03_g1[2]),
                         cbind(tabx$beta03_g1[3],tabx$lo03_g1[3],tabx$hi03_g1[3]),
                         cbind(tabx$beta03_g1[4],tabx$lo03_g1[4],tabx$hi03_g1[4]),
                         cbind(tabx$beta03_g1[5],tabx$lo03_g1[5],tabx$hi03_g1[5]),
                         cbind(tabx$beta03_g1[6],tabx$lo03_g1[6],tabx$hi03_g1[6]),
                         cbind(tabx$beta03_g1[7],tabx$lo03_g1[7],tabx$hi03_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(4,4,4,4,4,4,4),
                   rbind(tab,cbind(tabx$beta04_g1[1],tabx$lo04_g1[1],tabx$hi04_g1[1]),
                         cbind(tabx$beta04_g1[2],tabx$lo04_g1[2],tabx$hi04_g1[2]),
                         cbind(tabx$beta04_g1[3],tabx$lo04_g1[3],tabx$hi04_g1[3]),
                         cbind(tabx$beta04_g1[4],tabx$lo04_g1[4],tabx$hi04_g1[4]),
                         cbind(tabx$beta04_g1[5],tabx$lo04_g1[5],tabx$hi04_g1[5]),
                         cbind(tabx$beta04_g1[6],tabx$lo04_g1[6],tabx$hi04_g1[6]),
                         cbind(tabx$beta04_g1[7],tabx$lo04_g1[7],tabx$hi04_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(5,5,5,5,5,5,5),
                   rbind(tab,cbind(tabx$beta05_g1[1],tabx$lo05_g1[1],tabx$hi05_g1[1]),
                         cbind(tabx$beta05_g1[2],tabx$lo05_g1[2],tabx$hi05_g1[2]),
                         cbind(tabx$beta05_g1[3],tabx$lo05_g1[3],tabx$hi05_g1[3]),
                         cbind(tabx$beta05_g1[4],tabx$lo05_g1[4],tabx$hi05_g1[4]),
                         cbind(tabx$beta05_g1[5],tabx$lo05_g1[5],tabx$hi05_g1[5]),
                         cbind(tabx$beta05_g1[6],tabx$lo05_g1[6],tabx$hi05_g1[6]),
                         cbind(tabx$beta05_g1[7],tabx$lo05_g1[7],tabx$hi05_g1[7])),tabx$X,tabx$class_g1))
  colnames(tab)<-c("year","pred_diff","lci","uci","out","class")
  tab<-as.data.frame(tab)
  tab$pred_diff<-as.numeric(tab$pred_diff)
  tab$lci<-as.numeric(tab$lci)
  tab$uci<-as.numeric(tab$uci)
  tab$coef<-ic_guapa2(guapa(tab$pred_diff),guapa(tab$lci),guapa(tab$uci))
  tab$class<-with(tab,ifelse(class=="Control arm, <10 vs. >=10","0",
                             ifelse(class=="MedDiet groups, <10 vs. >=10","1",
                                    ifelse(class=="Yes treatment, <10 vs. >=10","2",
                                           ifelse(class=="No treatment, <10 vs. >=10","3",
                                                  ifelse(class=="Yes condition, <10 vs. >=10","4",
                                                         ifelse(class=="No condition, <10 vs. >=10","5",
                                                                ifelse(class=="<10 vs. >=10","6",NA))))))))
  tab$class<-as.factor(tab$class)
  namefile<-paste("./Results/Outputs/Repeated/f_",vars03[i],".csv",sep="")
  write.table(tab,file=namefile,sep=";",col.names=NA)
  
}


vars01<-c("ldl","hdl","tg")
vars02<-c(2,2,4)

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Results/Outputs/Repeated/f_",vars01[i],".csv",sep="")
  dat<-read.csv2(namefile,header=TRUE,sep=";",dec=".")
  dat<-subset2(dat,"dat$class==6")
  dat$class<-as.factor(dat$class)
  label<-dat$out[1]
  
  figure<-ggplot() +
    geom_hline(yintercept=0, linetype=2) +
    geom_point(data=dat, aes(x=year, y=pred_diff, col=class), size = 3.5, shape = 15, position=position_dodge(width = 0.8)) +
    geom_linerange(data=dat, aes(x=year, y=pred_diff, ymin=lci, ymax=uci, col=class), size=0.8, position=position_dodge(width = 0.8)) +
    geom_errorbar(data=dat, aes(x=year, ymin=lci, ymax=uci, col=class), width=0.3, size=0.8, position=position_dodge(width = 0.8)) + 
    coord_flip() +
    geom_text(data=dat, size=5, aes(y=max(uci)*vars02[i], x=year, label=coef, hjust='inward', col=class), position = position_dodge(0.8)) +
    scale_x_continuous(breaks = dat$year) +
    xlab("Follow-up time (years)") +
    ylab(paste("Inter-group diff., ",label,sep="")) +
    theme_minimal() +
    scale_colour_manual(name="",
                        values=c('#D55E00')) +
    theme(panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          panel.background = element_blank(),
          axis.line=element_line(colour = "black"),
          axis.text.y=element_text(size=14),
          axis.text.x=element_text(size=14),
          axis.ticks.y=element_line(),
          axis.ticks.x=element_line(),
          axis.title.x=element_text(size=18, face="bold"),
          axis.title.y=element_text(size=18, face="bold"),
          legend.position="none",
          legend.title=element_blank(),
          legend.text=element_text(size=10),
          legend.justification="center")
  
  namefile2<-paste("./Results/Outputs/Repeated/",vars01[i],"_forest_main.jpg",sep="")
  ggsave(filename=namefile2, units="px", width=8400, height=8400, dpi=1200, bg="white")
  figure
}


vars01<-c("ldl","hdl","tg")
vars02<-c(2,2,8)
vars03<-c("Statin users (baseline)","Fibrate users (baseline)","Fibrate users (baseline)")
vars04<-c("Statin non-users (baseline)","Fibrate non-users (baseline)","Fibrate non-users (baseline)")
vars05<-c(">=160 mg/dL (baseline)","Low HDL-C (baseline)",">=150 mg/dL (baseline)")
vars06<-c("<160 mg/dL (baseline)","Non-low HDL-C (baseline)","<150 mg/dL (baseline)")

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Results/Outputs/Repeated/f_",vars01[i],".csv",sep="")
  dat<-read.csv2(namefile,header=TRUE,sep=";",dec=".")
  dat<-subset2(dat,"dat$class==2 | dat$class==3 | dat$class==4 | dat$class==5 | dat$class==6")
  dat$class<-as.factor(dat$class)
  label<-dat$out[1]
  
  figure<-ggplot() +
    geom_hline(yintercept=0, linetype=2) +
    geom_point(data=dat, aes(x=year, y=pred_diff, col=class), size = 2.5, shape = 15, position=position_dodge(width = 0.8)) +
    geom_linerange(data=dat, aes(x=year, y=pred_diff, ymin=lci, ymax=uci, col=class), size=0.6, position=position_dodge(width = 0.8)) +
    coord_flip() +
    geom_text(data=dat, size=4, aes(y=max(uci)*vars02[i], x=year, label=coef, hjust='inward', col=class), position = position_dodge(0.8)) +
    scale_x_continuous(breaks = dat$year) +
    xlab("Follow-up time (years)") +
    ylab(paste("Inter-group diff., ",label,sep="")) +
    theme_minimal() +
    scale_colour_manual(name="",
                        values=c('#882255','#117733','#5833ff','#de026e','#D55E00'),
                        labels=c(vars03[i],vars04[i],vars05[i],vars06[i],"All participants")) +
    theme(panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          panel.background = element_blank(),
          axis.line=element_line(colour = "black"),
          axis.text.y=element_text(size=12),
          axis.text.x=element_text(size=12),
          axis.ticks.y=element_line(),
          axis.ticks.x=element_line(),
          axis.title.x=element_text(size=15, face="bold"),
          axis.title.y=element_text(size=15, face="bold"),
          legend.position="right",
          legend.title=element_blank(),
          legend.text=element_text(size=10),
          legend.justification="center")
  
  namefile2<-paste("./Results/Outputs/Repeated/",vars01[i],"_forest_clin.jpg",sep="")
  ggsave(filename=namefile2, units="px", width=8400, height=8400, dpi=1200, bg="white")
  figure
}


vars01<-c("ldl","hdl","tg")
vars02<-c(2,2,-5)

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Results/Outputs/Repeated/f_",vars01[i],".csv",sep="")
  dat<-read.csv2(namefile,header=TRUE,sep=";",dec=".")
  dat<-subset2(dat,"dat$class==0 | dat$class==1 | dat$class==6")
  dat$class<-as.factor(dat$class)
  label<-dat$out[1]
  
  figure<-ggplot() +
    geom_hline(yintercept=0, linetype=2) +
    geom_point(data=dat, aes(x=year, y=pred_diff, col=class), size = 2.5, shape = 15, position=position_dodge(width = 0.8)) +
    geom_linerange(data=dat, aes(x=year, y=pred_diff, ymin=lci, ymax=uci, col=class), size=0.6, position=position_dodge(width = 0.8)) +
    coord_flip() +
    geom_text(data=dat, size=4, aes(y=max(uci)*vars02[i], x=year, label=coef, hjust='inward', col=class), position = position_dodge(0.8)) +
    scale_x_continuous(breaks = dat$year) +
    xlab("Follow-up time (years)") +
    ylab(paste("Inter-group diff., ",label,sep="")) +
    theme_minimal() +
    scale_colour_manual(name="",
                        values=c('#1065B1','#B31529','Black'),
                        labels=c("Control arm","MedDiet interventions","All participants")) +
    theme(panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          panel.background = element_blank(),
          axis.line=element_line(colour = "black"),
          axis.text.y=element_text(size=12),
          axis.text.x=element_text(size=12),
          axis.ticks.y=element_line(),
          axis.ticks.x=element_line(),
          axis.title.x=element_text(size=15, face="bold"),
          axis.title.y=element_text(size=15, face="bold"),
          legend.position="right",
          legend.title=element_blank(),
          legend.text=element_text(size=10),
          legend.justification="center")
  
  namefile2<-paste("./Results/Outputs/Repeated/",vars01[i],"_forest_grup.jpg",sep="")
  ggsave(filename=namefile2, units="px", width=8400, height=8400, dpi=1200, bg="white")
  figure
}



#########################
### SURVIVAL ANALYSES ###
#########################

load("./Results/Data/predimed_lipids.RData")

dat$edad70<-with(dat,ifelse(edad<70,0,1))
dat$escolar_sup<-with(dat,ifelse(escolar00==1,0,
                                 ifelse(escolar00==2,0,
                                        ifelse(escolar00==3,1,
                                               ifelse(escolar00==9,NA,NA)))))
dat$obesidad200<-with(dat,ifelse(obesidad00==2,1,0))
dat$af00_m<-with(dat,ifelse(af00<=median(dat$af00,na.rm=TRUE),0,1))
dat$kcal00_m<-with(dat,ifelse(kcal00<=median(dat$kcal00,na.rm=TRUE),0,1))
dat$grup_int2<-with(dat,ifelse(grup_int==3,0,1))
dat$tabaco200<-with(dat,ifelse(tabaco00==0,0,1)) # Never vs ever

z<-qnorm(1-0.05/2)


varsxx<-c("tg_hi150","tg_hi200","hdl_lo","ldl_hi100","ldl_hi130","ldl_hi160")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Onset of triglycerides >150 mg/dL",
          "Onset of triglycerides >200 mg/dL",
          "Onset of low HDL cholesterol",
          "Onset of LDL cholesterol >100 mg/dL",
          "Onset of LDL cholesterol >130 mg/dL",
          "Onset of LDL cholesterol >160 mg/dL")
vars09<-c("f_tg00","f_tg00","f_tg00","f_col00","f_col00","f_col00")
vars10<-c(8,8,8,8,8,8) # Most beneficial LTPA range (a posteriori)

for(i in 1:length(varsxx))
{
  vars01<-c(vars01,paste(varsxx[i],"_d",sep=""))
  vars03<-c(vars03,paste(varsxx[i],"_inicio",sep=""))
  vars05<-c(vars05,paste(varsxx[i],"_seg",sep=""))
}

for(i in 1:length(vars01))
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars04<-c(vars04,paste(vars01[i],"_when",sep=""))
  vars06<-c(vars06,paste("to",vars01[i],"_left",sep=""))
  vars07<-c(vars07,paste("to",vars01[i],"_right",sep=""))
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,(dat[,vars06[i]]+dat[,vars07[i]])/2,dat[,vars02[i]]))
}


tab<-NULL
tab_ok<-NULL

for(i in 1:length(vars01))
  
{ 
  participants<-length(which(dat[,vars03[i]]==0))
  labelok<-vars08[i]
  datx<-subset2(dat,"dat[,vars03[i]]==0")
  
  datx$dmed_long<-with(datx,ifelse(datx[,vars04[i]]==0,dmed08_lx,
                                   ifelse(datx[,vars04[i]]==1,dmed01_lx,
                                          ifelse(datx[,vars04[i]]==2,dmed02_lx,
                                                 ifelse(datx[,vars04[i]]==3,dmed03_lx,
                                                        ifelse(datx[,vars04[i]]==4,dmed04_lx,
                                                               ifelse(datx[,vars04[i]]==5,dmed05_lx,
                                                                      ifelse(datx[,vars04[i]]==6,dmed06_lx,
                                                                             ifelse(datx[,vars04[i]]==7,dmed07_lx,
                                                                                    ifelse(datx[,vars04[i]]==8,dmed08_lx,NA))))))))))
  dmed_outl<-length(which(datx$dmed_long<5))
  datx<-subset2(datx,"datx$dmed_long>=5")
  samplesize<-dim(datx)[1]
  
  datx$dmed_long2<-with(datx,ifelse(dmed_long<10,0,
                                    ifelse(dmed_long>=10,1,NA)))

  dat2<-subset2(datx,"!is.na(datx$dmed_long)")
  median_time<-ic_guapa(guapa(summary((dat2[,vars02[i]]/365.25))[3]),guapa(summary((dat2[,vars02[i]]/365.25))[2]),guapa(summary((dat2[,vars02[i]]/365.25))[5]))
  
  mod02<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~dmed_long+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)
               +as.factor(diabetes00)+col00+hdl00+tg00+dat2[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat2)
  hr_dmed_long_cont<-intervals(mod02)[1,1]
  ic95a_dmed_long_cont<-intervals(mod02)[1,2]
  ic95b_dmed_long_cont<-intervals(mod02)[1,3]
  pval_dmed_long_cont<-intervals(mod02)[1,4]
  pval_dmed_long_cont_ex<-intervals(mod02)[1,4]
  hr_dmed_long_cont_ok<-guapa(hr_dmed_long_cont)
  ic95a_dmed_long_cont_ok<-guapa(ic95a_dmed_long_cont)
  ic95b_dmed_long_cont_ok<-guapa(ic95b_dmed_long_cont)
  coef_dmed_long_cont<-ic_guapa2(hr_dmed_long_cont_ok,ic95a_dmed_long_cont_ok,ic95b_dmed_long_cont_ok)
  pval_dmed_long_cont<-pval_guapa(pval_dmed_long_cont)
  
  nval_dmed_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$dmed_long)))
  nval_dmed_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$dmed_long)))
  nval_dmed_long_cont<-paste("'",nval_dmed_long_ca,"/",nval_dmed_long_ca+nval_dmed_long_co,sep="")

  dat3<-subset2(datx,"datx$dmed_long<vars10[i]")
  dat3$xxx<-dat3$dmed_long/1
  modxx<-coxph(Surv(dat3[,vars02[i]], dat3[,vars01[i]])~xxx+as.factor(grup_int)+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)
               +as.factor(diabetes00)+col00+hdl00+tg00+dat3[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=dat3)
  hr_dmed_long_opt<-intervals(modxx)[1,1]
  ic95a_dmed_long_opt<-intervals(modxx)[1,2]
  ic95b_dmed_long_opt<-intervals(modxx)[1,3]
  pval_dmed_long_opt<-intervals(modxx)[1,4]
  pval_dmed_long_opt_ex<-intervals(modxx)[1,4]
  hr_dmed_long_opt_ok<-guapa(hr_dmed_long_opt)
  ic95a_dmed_long_opt_ok<-guapa(ic95a_dmed_long_opt)
  ic95b_dmed_long_opt_ok<-guapa(ic95b_dmed_long_opt)
  coef_dmed_long_opt<-ic_guapa2(hr_dmed_long_opt_ok,ic95a_dmed_long_opt_ok,ic95b_dmed_long_opt_ok)
  pval_dmed_long_opt<-pval_guapa(pval_dmed_long_opt)
  
  
  # SPLINES #
  
  mfit<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~pspline(dmed_long, df=4)+as.factor(grup_int)+cluster(idcluster2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)
              +as.factor(diabetes00)+col00+hdl00+tg00+dat2[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
              +af00+kcal00+prop_score01+prop_score02,
              na.action=na.exclude, method="breslow",data=dat2)
  
  p_lin_dmed<-pval_dmed_long_cont
  p_nonlin_dmed<-pval_guapa(summary(mfit)$coefficients[2,6])
  p_lrtest_dmed<-pval_guapa(lrtest(mod02,mfit)[2,5])
  
  p_lin2<-ifelse(p_lin_dmed=="<0.001"," < 0.001",
                 ifelse(p_lin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lin_dmed,sep="")))
  p_nonlin2<-ifelse(p_nonlin_dmed=="<0.001"," < 0.001",
                    ifelse(p_nonlin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_nonlin_dmed,sep="")))
  p_lrtest2<-ifelse(p_lrtest_dmed=="<0.001"," < 0.001",
                    ifelse(p_lrtest_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lrtest_dmed,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$dmed_long
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data$coef<-ic_guapa2(guapa(plot.data$y),guapa(plot.data$lci),guapa(plot.data$uci))
  min_dmed_val<-guapa(plot.data$x[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))])
  min_dmed_coef<-plot.data$coef[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))]
  plot.datax<-plot.data[,c("x","coef")]
  plot.data$coef<-NULL
  colnames(plot.datax)<-c("dmed","HR")
  write.table(plot.datax,file=paste("./Results/Outputs/Survival/backup/",vars01[i],".csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  namefile<-paste("./Results/Outputs/Survival/",vars01[i],".jpg",sep="")
  labely<-paste(vars08[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +1 score point (range: 5-14 points):\n",coef_dmed_long_cont,
             "\np-value for non-linearity",p_lrtest2,
             "\nHR for +1 score point (range: 5-",vars10[i]," points):\n",coef_dmed_long_opt,sep="")
  
  figure<-ggplot(data=plot.data, aes_string(x=plot.data$x, y=plot.data$y)) + 
    geom_ribbon(aes_string(ymin=plot.data$lci, ymax=plot.data$uci), alpha=0.25, fill='#D55E00') +
    geom_line(aes_string(x=plot.data$x, y=plot.data$y), color='#D55E00') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    #scale_x_continuous(breaks=c(5:14)) +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of MedDiet adherence\n(MedDiet adherence score points)"),y=labely) +
    annotate("text", x=max(plot.data$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  # INTERACTION TESTS #
  
  base<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~ns(dmed_long, df=4)+as.factor(grup_int2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)
              +as.factor(diabetes00)+col00+hdl00+tg00+dat2[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
              +af00+kcal00+prop_score01+prop_score02+cluster(idcluster2),
              na.action=na.exclude, method="breslow",data=dat2)
  grup<-coxph(Surv(dat2[,vars02[i]], dat2[,vars01[i]])~ns(dmed_long, df=4)+as.factor(grup_int2)+ns(dmed_long, df=4)*as.factor(grup_int2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)
              +as.factor(diabetes00)+col00+hdl00+tg00+dat2[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
              +af00+kcal00+prop_score01+prop_score02+cluster(idcluster2),
              na.action=na.exclude, method="breslow",data=dat2)
  p_int_grup<-pval_guapa(lrtest(base,grup)[2,5])
  
  # INTERACTION WITH GRUP_INT - SPLINES #
  
  datm<-subset2(dat2,"dat2$grup_int2==1")
  datc<-subset2(dat2,"dat2$grup_int2==0")
  
  mod02<-coxph(Surv(datm[,vars02[i]], datm[,vars01[i]])~dmed_long+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)
               +as.factor(diabetes00)+col00+hdl00+tg00+datm[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=datm)
  mfit<-coxph(Surv(datm[,vars02[i]], datm[,vars01[i]])~pspline(dmed_long, df=4)+cluster(idcluster2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)
              +as.factor(diabetes00)+col00+hdl00+tg00+datm[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
              +af00+kcal00+prop_score01+prop_score02,
              na.action=na.exclude, method="breslow",data=datm)
  
  datm$xxx<-datm$dmed_long/1
  modxx<-coxph(Surv(datm[,vars02[i]], datm[,vars01[i]])~xxx+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)
               +as.factor(diabetes00)+col00+hdl00+tg00+datm[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=datm)
  coef_m<-ic_guapa2(guapa(intervals(modxx)[1,1]),guapa(intervals(modxx)[1,2]),guapa(intervals(modxx)[1,3]))
  
  p_lin_dmed<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest_dmed<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linm<-ifelse(p_lin_dmed=="<0.001"," < 0.001",
                 ifelse(p_lin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lin_dmed,sep="")))
  p_nonlinm<-ifelse(p_lrtest_dmed=="<0.001"," < 0.001",
                    ifelse(p_lrtest_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lrtest_dmed,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$dmed_long
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_m<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_m)<-c("x","yest","lci","uci")
  plot.data_m$coef<-ic_guapa2(guapa(plot.data_m$y),guapa(plot.data_m$lci),guapa(plot.data_m$uci))
  plot.data_mx<-plot.data_m[,c("x","coef")]
  plot.data_m$coef<-NULL
  colnames(plot.data_mx)<-c("dmed","HR")
  write.table(plot.data_mx,file=paste("./Results/Outputs/Survival/backup/strat/",vars01[i],"_dmed.csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_m<-subset2(plot.data_m,"plot.data_m$uci<=3")
  #plot.data_m$class<-"1"
  
  mod02<-coxph(Surv(datc[,vars02[i]], datc[,vars01[i]])~dmed_long+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)
               +as.factor(diabetes00)+col00+hdl00+tg00+datc[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=datc)
  mfit<-coxph(Surv(datc[,vars02[i]], datc[,vars01[i]])~pspline(dmed_long, df=4)+cluster(idcluster2)
              +edad+strata(sexo)+strata(nodo)+strata(escolar00)
              +as.factor(diabetes00)+col00+hdl00+tg00+datc[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
              +af00+kcal00+prop_score01+prop_score02,
              na.action=na.exclude, method="breslow",data=datc)
  
  datc$xxx<-datc$dmed_long/2
  modxx<-coxph(Surv(datc[,vars02[i]], datc[,vars01[i]])~xxx+cluster(idcluster2)
               +edad+strata(sexo)+strata(nodo)+strata(escolar00)
               +as.factor(diabetes00)+col00+hdl00+tg00+datc[,vars09[i]]+as.factor(hta00)+as.factor(tabaco00)+bmi00
               +af00+kcal00+prop_score01+prop_score02,
               na.action=na.exclude, method="breslow", data=datc)
  coef_c<-ic_guapa2(guapa(intervals(modxx)[1,1]),guapa(intervals(modxx)[1,2]),guapa(intervals(modxx)[1,3]))
  
  p_lin_dmed<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest_dmed<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linc<-ifelse(p_lin_dmed=="<0.001"," < 0.001",
                 ifelse(p_lin_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lin_dmed,sep="")))
  p_nonlinc<-ifelse(p_lrtest_dmed=="<0.001"," < 0.001",
                    ifelse(p_lrtest_dmed=="<0.00001"," < 0.00001",paste(" = ",p_lrtest_dmed,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$dmed_long
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_c<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_c)<-c("x","yest","lci","uci")
  plot.data_c$coef<-ic_guapa2(guapa(plot.data_c$y),guapa(plot.data_c$lci),guapa(plot.data_c$uci))
  plot.data_cx<-plot.data_c[,c("x","coef")]
  plot.data_c$coef<-NULL
  colnames(plot.data_cx)<-c("dmed","HR")
  write.table(plot.data_cx,file=paste("./Results/Outputs/Survival/backup/strat/",vars01[i],"_cont.csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_c<-subset2(plot.data_c,"plot.data_c$uci<=3")
  #plot.data_c$class<-"0"
  
  plot.data<-rbind(plot.data_m,plot.data_c)
  namefile<-paste("./Results/Outputs/Survival/",vars01[i],"_grupint.jpg",sep="")
  labely<-paste(vars08[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("Mediterranean diet groups:",
             "\np-value for linearity",p_linm,
             "\n[HR for +1 score point: ",coef_m,"]",
             "\np-value for non-linearity",p_nonlinm,
             "\nLow-fat control arm:",
             "\np-value for linearity",p_linc,
             "\n[HR for +1 score point: ",coef_c,"]",
             "\np-value for non-linearity",p_nonlinc,sep="")
  
  figure<-ggplot() + 
    geom_ribbon(aes(x=plot.data_m$x, y=plot.data_m$y, ymin=plot.data_m$lci, ymax=plot.data_m$uci), alpha=0.25, fill='#B31529') +
    geom_line(aes_string(x=plot.data_m$x, y=plot.data_m$y), color='#B31529') +
    geom_ribbon(aes(x=plot.data_c$x, y=plot.data_c$y, ymin=plot.data_c$lci, ymax=plot.data_c$uci), alpha=0.25, fill='#1065B1') +
    geom_line(aes_string(x=plot.data_c$x, y=plot.data_c$y), color='#1065B1') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    #scale_x_continuous(breaks=c(5:14)) +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of MedDiet adherence\n(MedDiet adherence score points)"),y=labely) +
    annotate("text", x=max(plot.data_m$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  tab_ok<-rbind(tab_ok,cbind(median_time,participants,dmed_outl,
                             nval_dmed_long_cont,coef_dmed_long_cont,pval_dmed_long_cont,pval_dmed_long_cont_ex,p_lrtest_dmed,
                             min_dmed_val,min_dmed_coef,labelok,
                             p_int_grup))
  tab<-rbind(tab,cbind(median_time,participants,dmed_outl,
                       nval_dmed_long_cont,hr_dmed_long_cont,ic95a_dmed_long_cont,ic95b_dmed_long_cont,pval_dmed_long_cont,
                       pval_dmed_long_cont_ex,p_lrtest_dmed,
                       min_dmed_val,min_dmed_coef,labelok))
}

rownames(tab)<-vars01
rownames(tab_ok)<-vars01
write.table(tab_ok,file="./Results/Outputs/Survival/survival.csv",sep=";",col.names=NA)
write.table(tab,file="./Results/Outputs/Survival/forestplots.csv",sep=";",col.names=NA)


