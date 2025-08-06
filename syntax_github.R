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

load("./Data/predimed_lipids_long.RData")

age_counts <- dat_long %>% 
  mutate(age_int = floor(age)) %>% 
  filter(age_int >= 55 & age_int <= 80) %>% 
  group_by(age_int) %>% 
  summarise(
    across(c(tg, hdl, ldl),
           ~ sum(!is.na(.x)),
           .names = "rows_with_{.col}"),
    .groups = "drop"
  )

write.table(age_counts,file="./Outputs/Descriptive/age_measures_values.csv",sep=";",col.names=NA)


###########################
### MIXED LINEAR MODELS ###
###########################

dir.create("C:/Users/Alvaro/Documents/Documentos/Artículos/Montse - MedDiet and lipid profile/Outputs/Repeated")

#https://fromthebottomoftheheap.net/2021/02/02/random-effects-in-gams/

z<-qnorm(1-0.05/2)
se <- function(x) sqrt(var(x) / length(x))

vars00<-c("LDL cholesterol, mg/dL\n(predicted values, 95% CI)",
          "HDL cholesterol, mg/dL\n(predicted values, 95% CI)",
          "Triglycerides, mg/dL\n(predicted values, 95% CI)",
          "Non-HDL cholesterol, mg/dL\n(predicted values, 95% CI)")
vars01<-c("ldl","hdl","tg","nonhdl")
vars02<-c("ldl_basal","hdl_basal","tg_basal","nonhdl_basal")
vars03<-c("f_col_basal","f_tg_basal","f_tg_basal","f_col_basal")
vars05<-c("ldl_hi160_inicio","hdl_lo_inicio","tg_hi150_inicio","nonhdl_hi130_inicio")

# Usamos como covariables el uso de farmacos basal porque en las medidas repetidas hay NAs
# Usar las covariables tiempo-dependientes complica la prediccion

vars04<-c("55","56","57","58","59","60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80","81")

tab<-NULL
tab2<-NULL

for(i in 1:length(vars01))
  
{
  # 4 CATEGORIES - ALL PARTICIPANTS #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat4","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar+grup_int
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
  
  gam_predict<-expand.grid(group=factor(c(0,1,2,3)),
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat4,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)

  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  gam_predict2<-gam_predict[gam_predict$group==2,c("id","seg","fit")]
  gam_predict3<-gam_predict[gam_predict$group==3,c("id","seg","fit")]
  
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
  
  group2<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict2[gam_predict2$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group2<-as.data.frame(rbind(group2,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group2)<-c("seg","group2_fit","group2_lo","group2_hi")
  
  group3<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict3[gam_predict3$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group3<-as.data.frame(rbind(group3,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group3)<-c("seg","group3_fit","group3_lo","group3_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  plot.data<-merge2(plot.data,group2,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  plot.data<-merge2(plot.data,group3,by.id=c("seg"),all.x=TRUE,sort=FALSE)
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
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#56B4E9") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#56B4E9') +
    geom_ribbon(aes_string(ymin='group2_lo', ymax='group2_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group2_fit'), color='#0072B2') +
    geom_ribbon(aes_string(ymin='group3_lo', ymax='group3_hi'), alpha=0.25, fill="#009E73") +
    geom_line(aes_string(x='seg', y='group3_fit'), color='#009E73') +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Age (years)"),y=vars00[i]) +
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
  
  namefile<-paste("./Outputs/Repeated/",vars01[i],"_cat4.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("8-<10 vs. 8")
  class_g2<-c("10-<12 vs. 8")
  class_g3<-c(">=12 vs. 8")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  beta55_g2<-intervals(mod55)[3,1]
  lo55_g2<-intervals(mod55)[3,2]
  hi55_g2<-intervals(mod55)[3,3]
  coef55_g2<-ic_guapa2(guapa(beta55_g2),guapa(lo55_g2),guapa(hi55_g2))
  pval55_g2<-pval_guapa(intervals(mod55)[3,4])
  beta60_g2<-intervals(mod60)[3,1]
  lo60_g2<-intervals(mod60)[3,2]
  hi60_g2<-intervals(mod60)[3,3]
  coef60_g2<-ic_guapa2(guapa(beta60_g2),guapa(lo60_g2),guapa(hi60_g2))
  pval60_g2<-pval_guapa(intervals(mod60)[3,4])
  beta65_g2<-intervals(mod65)[3,1]
  lo65_g2<-intervals(mod65)[3,2]
  hi65_g2<-intervals(mod65)[3,3]
  coef65_g2<-ic_guapa2(guapa(beta65_g2),guapa(lo65_g2),guapa(hi65_g2))
  pval65_g2<-pval_guapa(intervals(mod65)[3,4])
  beta70_g2<-intervals(mod70)[3,1]
  lo70_g2<-intervals(mod70)[3,2]
  hi70_g2<-intervals(mod70)[3,3]
  coef70_g2<-ic_guapa2(guapa(beta70_g2),guapa(lo70_g2),guapa(hi70_g2))
  pval70_g2<-pval_guapa(intervals(mod70)[3,4])
  beta75_g2<-intervals(mod75)[3,1]
  lo75_g2<-intervals(mod75)[3,2]
  hi75_g2<-intervals(mod75)[3,3]
  coef75_g2<-ic_guapa2(guapa(beta75_g2),guapa(lo75_g2),guapa(hi75_g2))
  pval75_g2<-pval_guapa(intervals(mod75)[3,4])
  beta80_g2<-intervals(mod80)[3,1]
  lo80_g2<-intervals(mod80)[3,2]
  hi80_g2<-intervals(mod80)[3,3]
  coef80_g2<-ic_guapa2(guapa(beta80_g2),guapa(lo80_g2),guapa(hi80_g2))
  pval80_g2<-pval_guapa(intervals(mod80)[3,4])

  beta55_g3<-intervals(mod55)[4,1]
  lo55_g3<-intervals(mod55)[4,2]
  hi55_g3<-intervals(mod55)[4,3]
  coef55_g3<-ic_guapa2(guapa(beta55_g3),guapa(lo55_g3),guapa(hi55_g3))
  pval55_g3<-pval_guapa(intervals(mod55)[4,4])
  beta60_g3<-intervals(mod60)[4,1]
  lo60_g3<-intervals(mod60)[4,2]
  hi60_g3<-intervals(mod60)[4,3]
  coef60_g3<-ic_guapa2(guapa(beta60_g3),guapa(lo60_g3),guapa(hi60_g3))
  pval60_g3<-pval_guapa(intervals(mod60)[4,4])
  beta65_g3<-intervals(mod65)[4,1]
  lo65_g3<-intervals(mod65)[4,2]
  hi65_g3<-intervals(mod65)[4,3]
  coef65_g3<-ic_guapa2(guapa(beta65_g3),guapa(lo65_g3),guapa(hi65_g3))
  pval65_g3<-pval_guapa(intervals(mod65)[4,4])
  beta70_g3<-intervals(mod70)[4,1]
  lo70_g3<-intervals(mod70)[4,2]
  hi70_g3<-intervals(mod70)[4,3]
  coef70_g3<-ic_guapa2(guapa(beta70_g3),guapa(lo70_g3),guapa(hi70_g3))
  pval70_g3<-pval_guapa(intervals(mod70)[4,4])
  beta75_g3<-intervals(mod75)[4,1]
  lo75_g3<-intervals(mod75)[4,2]
  hi75_g3<-intervals(mod75)[4,3]
  coef75_g3<-ic_guapa2(guapa(beta75_g3),guapa(lo75_g3),guapa(hi75_g3))
  pval75_g3<-pval_guapa(intervals(mod75)[4,4])
  beta80_g3<-intervals(mod80)[4,1]
  lo80_g3<-intervals(mod80)[4,2]
  hi80_g3<-intervals(mod80)[4,3]
  coef80_g3<-ic_guapa2(guapa(beta80_g3),guapa(lo80_g3),guapa(hi80_g3))
  pval80_g3<-pval_guapa(intervals(mod80)[4,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab<-rbind(tab,cbind(class_g2,beta55_g2,lo55_g2,hi55_g2,beta60_g2,lo60_g2,hi60_g2,beta65_g2,lo65_g2,hi65_g2,
                       beta70_g2,lo70_g2,hi70_g2,beta75_g2,lo75_g2,hi75_g2,beta80_g2,lo80_g2,hi80_g2))
  tab<-rbind(tab,cbind(class_g3,beta55_g3,lo55_g3,hi55_g3,beta60_g3,lo60_g3,hi60_g3,beta65_g3,lo65_g3,hi65_g3,
                       beta70_g3,lo70_g3,hi70_g3,beta75_g3,lo75_g3,hi75_g3,beta80_g3,lo80_g3,hi80_g3))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  tab2<-rbind(tab2,cbind(class_g2,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g2,pval55_g2,coef60_g2,pval60_g2,coef65_g2,pval65_g2,
                         coef70_g2,pval70_g2,coef75_g2,pval75_g2,coef80_g2,pval80_g2))
  tab2<-rbind(tab2,cbind(class_g3,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g3,pval55_g3,coef60_g3,pval60_g3,coef65_g3,pval65_g3,
                         coef70_g3,pval70_g3,coef75_g3,pval75_g3,coef80_g3,pval80_g3))

  
  # 2 CATEGORIES - ALL PARTICIPANTS #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar+grup_int
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
    labs(x=c("Age (years)"),y=vars00[i]) +
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
  
  namefile<-paste("./Outputs/Repeated/",vars01[i],"_cat2.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("<10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))

  
  # 2 CATEGORIES - SEPARATION BETWEEN CONDITION AT BASELINE #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02",vars05[i])]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02","strat")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_gam01<-lme(variable~bs(seg,df=4)*group+strat+sexo+escolar+grup_int
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  mod_gam02<-lme(variable~bs(seg,df=4)*group*strat+sexo+escolar+grup_int
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  pval_int<-pval_guapa(lrtest(mod_gam01,mod_gam02)[2,5])
  
  # NO CONDITION AT BASELINE #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars05[i]]==0")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar+grup_int
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("No condition, <10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  
  # YES CONDITION AT BASELINE #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars05[i]]==1")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar+grup_int
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("Yes condition, <10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  
  
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
    labs(x=c("Age (years)"),y=vars00[i]) +
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
  
  namefile<-paste("./Outputs/Repeated/",vars01[i],"_cat2_cond_baseline.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  
  # 2 CATEGORIES - SEPARATION BETWEEN TREATMENT AT BASELINE #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_gam01<-lme(variable~bs(seg,df=4)*group+tt+sexo+escolar+grup_int
                 +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  mod_gam02<-lme(variable~bs(seg,df=4)*group*tt+sexo+escolar+grup_int
                 +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  pval_int<-pval_guapa(lrtest(mod_gam01,mod_gam02)[2,5])
  
  # NO TREATMENT AT BASELINE #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars03[i]]==0")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal","hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar+grup_int
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("No treatment, <10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  
  
  # YES CONDITION AT BASELINE #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long[,vars03[i]]==1")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal","hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+sexo+escolar+grup_int
               +diabetes+col+hdl+tg+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar+grup_int
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("Yes treatment, <10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  

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
    labs(x=c("Age (years)"),y=vars00[i]) +
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
  
  namefile<-paste("./Outputs/Repeated/",vars01[i],"_cat2_tt_baseline.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  
  # 2 CATEGORIES - SEPARATION BETWEEN PREDIMED INTERVENTION GROUP #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]])")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_gam01<-lme(variable~bs(seg,df=4)*group+grup_int+sexo+escolar
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  mod_gam02<-lme(variable~bs(seg,df=4)*group*grup_int+sexo+escolar
                 +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
                 random = ~1 | id2, 
                 correlation = corCAR1(form = ~seg | id2), 
                 control = lmeControl(opt="optim"), 
                 data=xxx,
                 method='REML',
                 na.action=na.exclude)
  pval_int<-pval_guapa(lrtest(mod_gam01,mod_gam02)[2,5])
  
  # MEDDIET INTERVENTION GROUPS #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long$grup_int2==1")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("MedDiet groups, <10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  
  # CONTROL ARM #
  
  load("./Data/predimed_lipids_long.RData")
  dat_long<-subset2(dat_long,"!is.na(dat_long[,vars02[i]]) & dat_long$grup_int2==0")
  xxx<-dat_long[,c("id",vars01[i],"dmed_long_cat2","age","sexo","escolar00",
                   "diabetes00","col_basal","hdl_basal","tg_basal",vars03[i],"hta00","tabaco200",
                   "bmi00","af00","kcal00","prop_score01","prop_score02")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  
  mod_lin<-lme(variable~seg*group+sexo+escolar
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_par<-lme(variable~bs(seg,df=4)+group+sexo+escolar
               +diabetes+col+hdl+tg+tt+hta+tabaco+imc+actfis+kcal+ps01+ps02, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt="optim"), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  mod_gam<-lme(variable~bs(seg,df=4)*group+sexo+escolar
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
                           seg=seq(55,81,by=1),
                           id=unique(dat_long$id))
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$dmed_long_cat2,dat_long$sexo,dat_long$escolar00,
                                  dat_long$diabetes00,dat_long$col_basal,dat_long$hdl_basal,dat_long$tg_basal,dat_long[,vars03[i]],
                                  dat_long$hta00,dat_long$tabaco200,dat_long$bmi00,dat_long$af00,dat_long$kcal00,
                                  dat_long$prop_score01,dat_long$prop_score02)))
  names(xxx)<-c("id","group_ok","sexo","escolar",
                "diabetes","col","hdl","tg","tt","hta","tabaco","imc","actfis","kcal","ps01","ps02")
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  
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
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==55 | gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v55","v60","v65","v70","v75","v80")
  
  mod55<-lm(v55~as.factor(group),data=gam_predictx)
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)

  class_g1<-c("Control arm, <10 vs. >=10")
  
  beta55_g1<-intervals(mod55)[2,1]
  lo55_g1<-intervals(mod55)[2,2]
  hi55_g1<-intervals(mod55)[2,3]
  coef55_g1<-ic_guapa2(guapa(beta55_g1),guapa(lo55_g1),guapa(hi55_g1))
  pval55_g1<-pval_guapa(intervals(mod55)[2,4])
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])

  tab<-rbind(tab,cbind(class_g1,beta55_g1,lo55_g1,hi55_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                       beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,pval_int,coef55_g1,pval55_g1,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1))
  
  
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
    labs(x=c("Age (years)"),y=vars00[i]) +
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
  
  namefile<-paste("./Outputs/Repeated/",vars01[i],"_cat2_interv_group.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
}

rownames(tab)<-c("LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)",
                 "LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)","LDL cholesterol (mg/dL)",
                 "HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)",
                 "HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)","HDL cholesterol (mg/dL)",
                 "triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)",
                 "triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)","triglycerides (mg/dL)",
                 "non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)",
                 "non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)","non-HDL cholesterol (mg/dL)")
rownames(tab2)<-c("LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C","LDL-C",
                 "HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C","HDL-C",
                 "TG","TG","TG","TG","TG","TG","TG","TG","TG","TG",
                 "NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C","NonHDL-C")
write.table(tab,file="./Outputs/Repeated/forestplots.csv",sep=";",col.names=NA)
write.table(tab2,file="./Outputs/Repeated/repeated.csv",sep=";",col.names=NA)



######################################################
### FOREST PLOTS OF DIFFERENCES IN PREDICTED MEANS ###
######################################################

dat<-read.csv2("./Outputs/Repeated/forestplots.csv",header=TRUE,sep=";",dec=".")

vars01<-c(4,14,24,34)
vars02<-c(10,20,30,40)
vars03<-c("ldl","hdl","tg","nonhdl")

for(i in 1:length(vars01))
  
{
  tabx<-dat[vars01[i]:vars02[i],]
  tab<-NULL
  tab<-rbind(cbind(c(55,55,55,55,55,55,55),
                   rbind(tab,cbind(tabx$beta55_g1[1],tabx$lo55_g1[1],tabx$hi55_g1[1]),
                         cbind(tabx$beta55_g1[2],tabx$lo55_g1[2],tabx$hi55_g1[2]),
                         cbind(tabx$beta55_g1[3],tabx$lo55_g1[3],tabx$hi55_g1[3]),
                         cbind(tabx$beta55_g1[4],tabx$lo55_g1[4],tabx$hi55_g1[4]),
                         cbind(tabx$beta55_g1[5],tabx$lo55_g1[5],tabx$hi55_g1[5]),
                         cbind(tabx$beta55_g1[6],tabx$lo55_g1[6],tabx$hi55_g1[6]),
                         cbind(tabx$beta55_g1[7],tabx$lo55_g1[7],tabx$hi55_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(60,60,60,60,60,60,60),
                   rbind(tab,cbind(tabx$beta60_g1[1],tabx$lo60_g1[1],tabx$hi60_g1[1]),
                         cbind(tabx$beta60_g1[2],tabx$lo60_g1[2],tabx$hi60_g1[2]),
                         cbind(tabx$beta60_g1[3],tabx$lo60_g1[3],tabx$hi60_g1[3]),
                         cbind(tabx$beta60_g1[4],tabx$lo60_g1[4],tabx$hi60_g1[4]),
                         cbind(tabx$beta60_g1[5],tabx$lo60_g1[5],tabx$hi60_g1[5]),
                         cbind(tabx$beta60_g1[6],tabx$lo60_g1[6],tabx$hi60_g1[6]),
                         cbind(tabx$beta60_g1[7],tabx$lo60_g1[7],tabx$hi60_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(65,65,65,65,65,65,65),
                   rbind(tab,cbind(tabx$beta65_g1[1],tabx$lo65_g1[1],tabx$hi65_g1[1]),
                         cbind(tabx$beta65_g1[2],tabx$lo65_g1[2],tabx$hi65_g1[2]),
                         cbind(tabx$beta65_g1[3],tabx$lo65_g1[3],tabx$hi65_g1[3]),
                         cbind(tabx$beta65_g1[4],tabx$lo65_g1[4],tabx$hi65_g1[4]),
                         cbind(tabx$beta65_g1[5],tabx$lo65_g1[5],tabx$hi65_g1[5]),
                         cbind(tabx$beta65_g1[6],tabx$lo65_g1[6],tabx$hi65_g1[6]),
                         cbind(tabx$beta65_g1[7],tabx$lo65_g1[7],tabx$hi65_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(70,70,70,70,70,70,70),
                   rbind(tab,cbind(tabx$beta70_g1[1],tabx$lo70_g1[1],tabx$hi70_g1[1]),
                         cbind(tabx$beta70_g1[2],tabx$lo70_g1[2],tabx$hi70_g1[2]),
                         cbind(tabx$beta70_g1[3],tabx$lo70_g1[3],tabx$hi70_g1[3]),
                         cbind(tabx$beta70_g1[4],tabx$lo70_g1[4],tabx$hi70_g1[4]),
                         cbind(tabx$beta70_g1[5],tabx$lo70_g1[5],tabx$hi70_g1[5]),
                         cbind(tabx$beta70_g1[6],tabx$lo70_g1[6],tabx$hi70_g1[6]),
                         cbind(tabx$beta70_g1[7],tabx$lo70_g1[7],tabx$hi70_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(75,75,75,75,75,75,75),
                   rbind(tab,cbind(tabx$beta75_g1[1],tabx$lo75_g1[1],tabx$hi75_g1[1]),
                         cbind(tabx$beta75_g1[2],tabx$lo75_g1[2],tabx$hi75_g1[2]),
                         cbind(tabx$beta75_g1[3],tabx$lo75_g1[3],tabx$hi75_g1[3]),
                         cbind(tabx$beta75_g1[4],tabx$lo75_g1[4],tabx$hi75_g1[4]),
                         cbind(tabx$beta75_g1[5],tabx$lo75_g1[5],tabx$hi75_g1[5]),
                         cbind(tabx$beta75_g1[6],tabx$lo75_g1[6],tabx$hi75_g1[6]),
                         cbind(tabx$beta75_g1[7],tabx$lo75_g1[7],tabx$hi75_g1[7])),tabx$X,tabx$class_g1),
             cbind(c(80,80,80,80,80,80,80),
                   rbind(tab,cbind(tabx$beta80_g1[1],tabx$lo80_g1[1],tabx$hi80_g1[1]),
                         cbind(tabx$beta80_g1[2],tabx$lo80_g1[2],tabx$hi80_g1[2]),
                         cbind(tabx$beta80_g1[3],tabx$lo80_g1[3],tabx$hi80_g1[3]),
                         cbind(tabx$beta80_g1[4],tabx$lo80_g1[4],tabx$hi80_g1[4]),
                         cbind(tabx$beta80_g1[5],tabx$lo80_g1[5],tabx$hi80_g1[5]),
                         cbind(tabx$beta80_g1[6],tabx$lo80_g1[6],tabx$hi80_g1[6]),
                         cbind(tabx$beta80_g1[7],tabx$lo80_g1[7],tabx$hi80_g1[7])),tabx$X,tabx$class_g1))
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
  namefile<-paste("./Outputs/Repeated/f_",vars03[i],".csv",sep="")
  write.table(tab,file=namefile,sep=";",col.names=NA)
}


vars01<-c("ldl","hdl","tg","nonhdl")
vars02<-c(2,2,4,2)

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Outputs/Repeated/f_",vars01[i],".csv",sep="")
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
    xlab("Age (years)") +
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
  
  namefile2<-paste("./Outputs/Repeated/",vars01[i],"_forest_main.jpg",sep="")
  ggsave(filename=namefile2, units="px", width=8400, height=8400, dpi=1200, bg="white")
  figure
}


vars01<-c("ldl","hdl","tg","nonhdl")
vars02<-c(2,2.2,3,2)
vars03<-c("Statin users (baseline)","Fibrate users (baseline)","Fibrate users (baseline)","Statin users (baseline)")
vars04<-c("Statin non-users (baseline)","Fibrate non-users (baseline)","Fibrate non-users (baseline)","Statin non-users (baseline)")
vars05<-c(">=160 mg/dL (baseline)","Low HDL-C (baseline)",">=150 mg/dL (baseline)",">=130 mg/dL (baseline)")
vars06<-c("<160 mg/dL (baseline)","Non-low HDL-C (baseline)","<150 mg/dL (baseline)","<130 mg/dL (baseline)")

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Outputs/Repeated/f_",vars01[i],".csv",sep="")
  dat<-read.csv2(namefile,header=TRUE,sep=";",dec=".")
  dat<-subset2(dat,"dat$class==2 | dat$class==3 | dat$class==4 | dat$class==5 | dat$class==6")
  dat$class<-as.factor(dat$class)
  label<-dat$out[1]
  dat$year<-factor(dat$year)
  pd<-position_dodge(width=0.7)
  
  figure<-ggplot() +
    geom_hline(yintercept=0, linetype=2) +
    geom_point(data=dat, aes(x=year, y=pred_diff, col=class), size = 2.5, shape = 15, position=pd) +
    geom_linerange(data=dat, aes(x=year, y=pred_diff, ymin=lci, ymax=uci, col=class), size=0.6, position=pd) +
    coord_flip() +
    geom_text(data=dat, size=4, aes(y=max(uci)*vars02[i], x=year, label=coef, hjust='inward', col=class), position=pd) +
    scale_x_discrete(breaks = levels(dat$year)) +
    xlab("Age (years)") +
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
  
  namefile2<-paste("./Outputs/Repeated/",vars01[i],"_forest_clin.jpg",sep="")
  ggsave(filename=namefile2, units="px", width=8400, height=8400, dpi=1200, bg="white")
  figure
}


vars01<-c("ldl","hdl","tg","nonhdl")
vars02<-c(2,2,-5,2)

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Outputs/Repeated/f_",vars01[i],".csv",sep="")
  dat<-read.csv2(namefile,header=TRUE,sep=";",dec=".")
  dat<-subset2(dat,"dat$class==0 | dat$class==1 | dat$class==6")
  dat$class<-as.factor(dat$class)
  label<-dat$out[1]
  dat$year<-factor(dat$year)
  pd<-position_dodge(width=0.7)
  
  figure<-ggplot() +
    geom_hline(yintercept=0, linetype=2) +
    geom_point(data=dat, aes(x=year, y=pred_diff, col=class), size = 2.5, shape = 15, position=pd) +
    geom_linerange(data=dat, aes(x=year, y=pred_diff, ymin=lci, ymax=uci, col=class), size=0.6, position=pd) +
    coord_flip() +
    geom_text(data=dat, size=4, aes(y=max(uci)*vars02[i], x=year, label=coef, hjust='inward', col=class), position=pd) +
    scale_x_discrete(breaks = levels(dat$year)) +
    xlab("Age (years)") +
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
  
  namefile2<-paste("./Outputs/Repeated/",vars01[i],"_forest_grup.jpg",sep="")
  ggsave(filename=namefile2, units="px", width=8400, height=8400, dpi=1200, bg="white")
  figure
}



#########################
### SURVIVAL ANALYSES ###
#########################

library(WeightIt)
library(cobalt)
library(keras)
library(survminer)
library(ggpubr)

dir.create("C:/Users/Alvaro/Documents/Documentos/Artículos/Montse - MedDiet and lipid profile/Outputs/Kaplan_Meier")
dir.create("C:/Users/Alvaro/Documents/Documentos/Artículos/Montse - MedDiet and lipid profile/Outputs/Survival")
dir.create("C:/Users/Alvaro/Documents/Documentos/Artículos/Montse - MedDiet and lipid profile/Outputs/Survival/backup")
dir.create("C:/Users/Alvaro/Documents/Documentos/Artículos/Montse - MedDiet and lipid profile/Outputs/Survival/backup/strat")

load("./Data/predimed_lipids.RData")

dat$edad70<-with(dat,ifelse(edad<70,0,1))
dat$obesidad200<-with(dat,ifelse(obesidad00==2,1,0))
dat$af00_m<-with(dat,ifelse(af00<=median(dat$af00,na.rm=TRUE),0,1))
dat$kcal00_m<-with(dat,ifelse(kcal00<=median(dat$kcal00,na.rm=TRUE),0,1))

z<-qnorm(1-0.05/2)


varsxx<-c("tg_hi150","tg_hi200","hdl_lo","ldl_hi100","ldl_hi130","ldl_hi160")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Marginal cumulative incidence\nof triglycerides ≥150 mg/dL",
          "Marginal cumulative incidence\nof triglycerides ≥200 mg/dL",
          "Marginal cumulative incidence\nof low HDL cholesterol",
          "Marginal cumulative incidence\nof LDL cholesterol ≥100 mg/dL",
          "Marginal cumulative incidence\nof LDL cholesterol ≥130 mg/dL",
          "Marginal cumulative incidence\nof LDL cholesterol ≥160 mg/dL")
vars09<-c("f_tg00","f_tg00","f_tg00","f_col00","f_col00","f_col00")
vars10<-c(8,8,8,8,8,8) # Most beneficial LTPA range (a posteriori)
vars11<-c("Onset of triglycerides ≥150 mg/dL",
          "Onset of triglycerides ≥200 mg/dL",
          "Onset of low HDL cholesterol",
          "Onset of LDL cholesterol ≥100 mg/dL",
          "Onset of LDL cholesterol ≥130 mg/dL",
          "Onset of LDL cholesterol ≥160 mg/dL")

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

AGE_MIN <- 55
AGE_MAX <- 80

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
  datx$dmed_long4<-with(datx,ifelse(dmed_long<8,0,
                                   ifelse(dmed_long<10,1,
                                          ifelse(dmed_long<12,2,
                                                 ifelse(dmed_long>=12,3,NA)))))
  
  datx$start_age<-datx$age00
  datx$stop_age<-datx$age00+(datx[,vars02[i]]/365.25)
  datx$xxx<-datx[, vars01[i]]
  datx$yyy<-datx[, vars09[i]]
  
  datx <- datx |>
    dplyr::mutate(
      entry_age = pmax(start_age, AGE_MIN),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  
  dat2<-subset2(datx,"!is.na(datx$dmed_long)")
  median_time<-ic_guapa(guapa(summary((dat2[,vars02[i]]/365.25))[3]),guapa(summary((dat2[,vars02[i]]/365.25))[2]),guapa(summary((dat2[,vars02[i]]/365.25))[5]))

  
  # KAPLAN-MEIER CURVES #
  
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(dmed_long2), base = 1) +
      as.factor(grup_int)  + as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  
  coef<-paste("Multivariable Cox model,\nhigh vs. low adherence:\nHR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- dmed_long2 ~
    as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) +
    as.factor(diabetes00) + col00 + hdl00 + tg00 +
    as.factor(hta00) + as.factor(tabaco00) + bmi00 + af00 + kcal00 +
    prop_score01 + prop_score02 + as.factor(yyy)
  
  wt <- weightit(formula=ps_formula, data=dat2, method="ps", estimand="ATE", stabilize=TRUE)
  dat2$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~dmed_long2, data=dat2, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("black", "#D55E00"),
    legend.title   = " ",
    legend.labs    = c("Low adherence (<10 points)",
                       "High adherence (≥10 points)"),
    #legend = "bottom",
    legend = "none",
    xlim       = c(AGE_MIN, AGE_MAX),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = vars08[i],
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
    )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = AGE_MIN - 0.1,
             y      = 1,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 5)
  
  namefile<-paste("./Outputs/Kaplan_Meier/",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )

  
  # SURVIVAL ANALYSES #
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      dmed_long +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  hr_dmed_long_cont<-intervals(mod02)[1,1]
  ic95a_dmed_long_cont<-intervals(mod02)[1,2]
  ic95b_dmed_long_cont<-intervals(mod02)[1,3]
  pval_dmed_long_cont<-intervals(mod02)[1,4]
  pval_dmed_long_cont_ex<-intervals(mod02)[1,4]
  hr_dmed_long_cont_ok<-guapa(hr_dmed_long_cont)
  ic95a_dmed_long_cont_ok<-guapa(ic95a_dmed_long_cont)
  ic95b_dmed_long_cont_ok<-guapa(ic95b_dmed_long_cont)
  coef_dmed_long_cont<-ic_guapa2(hr_dmed_long_cont_ok,ic95a_dmed_long_cont_ok,ic95b_dmed_long_cont_ok)
  coef_dmed_long_cont2<-coef_dmed_long_cont
  pval_dmed_long_cont<-pval_guapa(pval_dmed_long_cont)
  
  mod03 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(dmed_long4),base=1) +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  hr_dmed_long_q2<-intervals(mod03)[1,1]
  ic95a_dmed_long_q2<-intervals(mod03)[1,2]
  ic95b_dmed_long_q2<-intervals(mod03)[1,3]
  pval_dmed_long_q2<-intervals(mod03)[1,4]
  hr_dmed_long_q2_ok<-guapa(hr_dmed_long_q2)
  ic95a_dmed_long_q2_ok<-guapa(ic95a_dmed_long_q2)
  ic95b_dmed_long_q2_ok<-guapa(ic95b_dmed_long_q2)
  coef_dmed_long_q2<-ic_guapa2(hr_dmed_long_q2_ok,ic95a_dmed_long_q2_ok,ic95b_dmed_long_q2_ok)
  pval_dmed_long_q2<-pval_guapa(pval_dmed_long_q2)
  hr_dmed_long_q3<-intervals(mod03)[2,1]
  ic95a_dmed_long_q3<-intervals(mod03)[2,2]
  ic95b_dmed_long_q3<-intervals(mod03)[2,3]
  pval_dmed_long_q3<-intervals(mod03)[2,4]
  hr_dmed_long_q3_ok<-guapa(hr_dmed_long_q3)
  ic95a_dmed_long_q3_ok<-guapa(ic95a_dmed_long_q3)
  ic95b_dmed_long_q3_ok<-guapa(ic95b_dmed_long_q3)
  coef_dmed_long_q3<-ic_guapa2(hr_dmed_long_q3_ok,ic95a_dmed_long_q3_ok,ic95b_dmed_long_q3_ok)
  pval_dmed_long_q3<-pval_guapa(pval_dmed_long_q3)
  hr_dmed_long_q4<-intervals(mod03)[3,1]
  ic95a_dmed_long_q4<-intervals(mod03)[3,2]
  ic95b_dmed_long_q4<-intervals(mod03)[3,3]
  pval_dmed_long_q4<-intervals(mod03)[3,4]
  hr_dmed_long_q4_ok<-guapa(hr_dmed_long_q4)
  ic95a_dmed_long_q4_ok<-guapa(ic95a_dmed_long_q4)
  ic95b_dmed_long_q4_ok<-guapa(ic95b_dmed_long_q4)
  coef_dmed_long_q4<-ic_guapa2(hr_dmed_long_q4_ok,ic95a_dmed_long_q4_ok,ic95b_dmed_long_q4_ok)
  pval_dmed_long_q4<-pval_guapa(pval_dmed_long_q4)
  
  mod03 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(dmed_long2),base=1) +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  hr_dmed_long_m<-intervals(mod03)[1,1]
  ic95a_dmed_long_m<-intervals(mod03)[1,2]
  ic95b_dmed_long_m<-intervals(mod03)[1,3]
  pval_dmed_long_m<-intervals(mod03)[1,4]
  hr_dmed_long_m_ok<-guapa(hr_dmed_long_m)
  ic95a_dmed_long_m_ok<-guapa(ic95a_dmed_long_m)
  ic95b_dmed_long_m_ok<-guapa(ic95b_dmed_long_m)
  coef_dmed_long_m<-ic_guapa2(hr_dmed_long_m_ok,ic95a_dmed_long_m_ok,ic95b_dmed_long_m_ok)
  pval_dmed_long_m<-pval_guapa(pval_dmed_long_m)
  
  mod04 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      dmed_long4 +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  hr_dmed_long_qi<-intervals(mod04)[1,1]
  ic95a_dmed_long_qi<-intervals(mod04)[1,2]
  ic95b_dmed_long_qi<-intervals(mod04)[1,3]
  pval_dmed_long_qi<-intervals(mod04)[1,4]
  hr_dmed_long_qi_ok<-guapa(hr_dmed_long_qi)
  ic95a_dmed_long_qi_ok<-guapa(ic95a_dmed_long_qi)
  ic95b_dmed_long_qi_ok<-guapa(ic95b_dmed_long_qi)
  coef_dmed_long_qi<-ic_guapa2(hr_dmed_long_qi_ok,ic95a_dmed_long_qi_ok,ic95b_dmed_long_qi_ok)
  pval_dmed_long_qi<-pval_guapa(pval_dmed_long_qi)
  
  nval_dmed_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$dmed_long)))
  nval_dmed_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$dmed_long)))
  nval_dmed_long_cont<-paste("'",nval_dmed_long_ca,"/",nval_dmed_long_ca+nval_dmed_long_co,sep="")
  nval_dmed_long_q<-table(dat2[,vars01[i]],by=dat2$dmed_long4)
  nval_dmed_long_q1<-paste("'",nval_dmed_long_q[2,1],"/",nval_dmed_long_q[2,1]+nval_dmed_long_q[1,1],sep="")
  nval_dmed_long_q2<-paste("'",nval_dmed_long_q[2,2],"/",nval_dmed_long_q[2,2]+nval_dmed_long_q[1,2],sep="")
  nval_dmed_long_q3<-paste("'",nval_dmed_long_q[2,3],"/",nval_dmed_long_q[2,3]+nval_dmed_long_q[1,3],sep="")
  nval_dmed_long_q4<-paste("'",nval_dmed_long_q[2,4],"/",nval_dmed_long_q[2,4]+nval_dmed_long_q[1,4],sep="")
  nval_dmed_long_m<-table(dat2[,vars01[i]],by=dat2$dmed_long2)
  nval_dmed_long_m1<-paste("'",nval_dmed_long_m[2,1],"/",nval_dmed_long_m[2,1]+nval_dmed_long_m[1,1],sep="")
  nval_dmed_long_m2<-paste("'",nval_dmed_long_m[2,2],"/",nval_dmed_long_m[2,2]+nval_dmed_long_m[1,2],sep="")
  
  dat3<-subset2(datx,"datx$dmed_long<vars10[i]")
  modxx <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      dmed_long +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat3,
    ties = "efron")
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
  
  
  # SURVIVAL SPLINES #
  
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(dmed_long, df=4) +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  
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
  write.table(plot.datax,file=paste("./Outputs/Survival/backup/",vars01[i],".csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  namefile<-paste("./Outputs/Survival/",vars01[i],".jpg",sep="")
  labely<-paste(vars11[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +1 score point (range: 5-14 points):\n",coef_dmed_long_cont2,
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
  
  base_grup <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df=4) + as.factor(grup_int2) +
      as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  grup <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df=4)*as.factor(grup_int2) +
      as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = dat2,
    ties = "efron")
  p_int_grup<-pval_guapa(lrtest(base_grup,grup)[2,5])
  
  base_edad <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df = 4) + as.factor(edad70) +
      as.factor(grup_int) +
      as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) +
      as.factor(hta00) + as.factor(tabaco00) + bmi00 +
      af00 + kcal00 + prop_score01 + prop_score02 +
      cluster(idcluster2),
    data = dat2, ties = "efron")
  edad <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df = 4) * as.factor(edad70) +
      as.factor(grup_int) +
      as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) +
      as.factor(hta00) + as.factor(tabaco00) + bmi00 +
      af00 + kcal00 + prop_score01 + prop_score02 +
      cluster(idcluster2),
    data = dat2, ties = "efron")
  p_int_edad <- pval_guapa(lrtest(base_edad, edad)[2, 5])
  
  base_sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df = 4) + as.factor(sexo) +
      as.factor(grup_int) +
      as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) +
      as.factor(hta00) + as.factor(tabaco00) + bmi00 +
      af00 + kcal00 + prop_score01 + prop_score02 +
      cluster(idcluster2),
    data = dat2, ties = "efron")
  sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df = 4) * as.factor(sexo) +
      as.factor(grup_int) +
      as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) +
      as.factor(hta00) + as.factor(tabaco00) + bmi00 +
      af00 + kcal00 + prop_score01 + prop_score02 +
      cluster(idcluster2),
    data = dat2, ties = "efron")
  p_int_sexo <- pval_guapa(lrtest(base_sexo, sexo)[2, 5])
  
  base_tt <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df = 4) + as.factor(yyy) +
      as.factor(grup_int) +
      as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + 
      as.factor(hta00) + as.factor(tabaco00) + bmi00 +
      af00 + kcal00 + prop_score01 + prop_score02 +
      cluster(idcluster2),
    data = dat2, ties = "efron")
  tt <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(dmed_long, df = 4)*as.factor(yyy) +
      as.factor(grup_int) +
      as.factor(sexo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + 
      as.factor(hta00) + as.factor(tabaco00) + bmi00 +
      af00 + kcal00 + prop_score01 + prop_score02 +
      cluster(idcluster2),
    data = dat2, ties = "efron")
  p_int_tt <- pval_guapa(lrtest(base_tt, tt)[2, 5])
  

  # INTERACTION WITH GRUP_INT - SPLINES #
  
  datm<-subset2(dat2,"dat2$grup_int2==1")
  datc<-subset2(dat2,"dat2$grup_int2==0")
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      dmed_long +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = datm,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(dmed_long, df=4) +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = datm,
    ties = "efron")
  coef_m<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  
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
  write.table(plot.data_mx,file=paste("./Outputs/Survival/backup/strat/",vars01[i],"_dmed.csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_m<-subset2(plot.data_m,"plot.data_m$uci<=3")
  #plot.data_m$class<-"1"

  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      dmed_long +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = datc,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(dmed_long, df=4) +
      as.factor(grup_int)  + as.factor(sexo) + strata(nodo) + as.factor(escolar00) +
      as.factor(diabetes00) + col00 + hdl00 + tg00 + as.factor(yyy) + as.factor(hta00) + 
      as.factor(tabaco00) + bmi00 + af00 + kcal00 + prop_score01 + prop_score02 + cluster(idcluster2),
    data = datc,
    ties = "efron")
  coef_c<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))

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
  write.table(plot.data_cx,file=paste("./Outputs/Survival/backup/strat/",vars01[i],"_cont.csv",sep=""),sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_c<-subset2(plot.data_c,"plot.data_c$uci<=3")
  #plot.data_c$class<-"0"
  
  plot.data<-rbind(plot.data_m,plot.data_c)
  namefile<-paste("./Outputs/Survival/",vars01[i],"_grupint.jpg",sep="")
  labely<-paste(vars11[i],"\n(multivariate adjusted hazard ratio)",sep="")
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
                             nval_dmed_long_q1,nval_dmed_long_q2,coef_dmed_long_q2,pval_dmed_long_q2,
                             nval_dmed_long_q3,coef_dmed_long_q3,pval_dmed_long_q3,
                             nval_dmed_long_q4,coef_dmed_long_q4,pval_dmed_long_q4,
                             coef_dmed_long_qi,pval_dmed_long_qi,
                             nval_dmed_long_m1,nval_dmed_long_m2,coef_dmed_long_m,pval_dmed_long_m,
                             min_dmed_val,min_dmed_coef,labelok,
                             p_int_grup,p_int_edad,p_int_sexo,p_int_tt))
  tab<-rbind(tab,cbind(median_time,participants,dmed_outl,
                       nval_dmed_long_cont,hr_dmed_long_cont,ic95a_dmed_long_cont,ic95b_dmed_long_cont,pval_dmed_long_cont,
                       pval_dmed_long_cont_ex,p_lrtest_dmed,
                       nval_dmed_long_q1,nval_dmed_long_q2,hr_dmed_long_q2,ic95a_dmed_long_q2,ic95b_dmed_long_q2,pval_dmed_long_q2,
                       nval_dmed_long_q3,hr_dmed_long_q3,ic95a_dmed_long_q3,ic95b_dmed_long_q3,pval_dmed_long_q3,
                       nval_dmed_long_q4,hr_dmed_long_q4,ic95a_dmed_long_q4,ic95b_dmed_long_q4,pval_dmed_long_q4,
                       hr_dmed_long_qi,ic95a_dmed_long_qi,ic95b_dmed_long_qi,pval_dmed_long_qi,
                       nval_dmed_long_m1,nval_dmed_long_m2,hr_dmed_long_m,ic95a_dmed_long_m,ic95b_dmed_long_m,pval_dmed_long_m,
                       min_dmed_val,min_dmed_coef,labelok))
}

rownames(tab)<-vars01
rownames(tab_ok)<-vars01
write.table(tab_ok,file="./Outputs/Survival/survival.csv",sep=";",col.names=NA)
write.table(tab,file="./Outputs/Survival/forestplots.csv",sep=";",col.names=NA)


