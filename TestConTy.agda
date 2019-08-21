{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import II using (PS; P; S)
open import EWRSg
open import Lib

module TestConTy (C' : Set) (T' : Set) where

Γ : Con
Γ = ∙ ▶S U -- Con
      ▶S ΠS (vz{S}) U -- Ty

Nil : TyP Γ
Nil = El (vs{S}{S} (vz{S}))

Γ' : Con
Γ' = Γ ▶P Nil -- nil

Γ''aux : Con
Γ''aux = Γ' ▶P El (vs{S}{P}{Γ} (vs{S}{S} (vz{S})))

Ext : TyP Γ'
Ext = ΠP {Γ'} (vs{S}{P}{Γ} (vs{S}{S}{∙ ▶S U} (vz{S})))
              (ΠP{Γ''aux} (appS{Γ'} (vs{S}{P}{Γ} (vz{S})))
                          (El (vs{S}{P}{Γ''aux} (vs{S}{P}{Γ'} (vs{S}{P}{Γ} (vs{S}{S}{∙ ▶S U} vz))))))

Γ'' : Con
Γ'' = Γ' ▶P Ext --ext

Unit : TyP Γ
Unit = ΠP (vs{S}{S}{∙ ▶S U} (vz{S})) (El (appS (vz{S}{∙ ▶ U})))

Γ''' : Con
Γ''' = Γ'' ▶P Unit [ wk{P}{Γ} ]TP [ wk{P}{Γ'} ]TP --unit

PiCon : TmS Γ'' U
PiCon = vs{S}{P}{Γ'} (vs{S}{P}{Γ} (vs{S}{S}{∙ ▶S U} (vz{S})))

PiTy : TmS Γ'' (ΠS PiCon U)
PiTy = vs{S}{P}{Γ'} (vs{S}{P}{Γ} (vz{S}))

PiA : TmS (Γ'' ▶P El PiCon) U
PiA = appS PiTy

PiΓACon : TmS (Γ'' ▶P El PiCon ▶P El PiA) U
PiΓACon = vs{S}{P}{Γ'' ▶P El PiCon} (vs{S}{P}{Γ''} PiCon)

PiΓATy : TmS (Γ'' ▶P El PiCon ▶P El PiA) (ΠS PiΓACon U)
PiΓATy = vs{S}{P}{Γ'' ▶P El PiCon} (vs{S}{P}{Γ''} PiTy)

PiExtΓ : TmP (Γ'' ▶P El PiCon) (ΠP PiA (El PiΓACon))
PiExtΓ = appP (vz{P}{Γ'}{Ext})

PiExtΓA : TmP (Γ'' ▶P El PiCon ▶P El PiA) (El PiΓACon)
PiExtΓA = appP PiExtΓ

PiB : TmS (Γ'' ▶P El PiCon ▶P El PiA) U
PiB = atS{Γ'' ▶P El PiCon ▶P El PiA}{PiΓACon}{U} PiΓATy PiExtΓA

PiRet : TmS (Γ'' ▶P El PiCon ▶P El PiA ▶P El PiB) U
PiRet = vs{S}{P}{Γ'' ▶P El PiCon ▶P El PiA} (vs{S}{P}{Γ'' ▶P El PiCon} PiA)

Pi : TyP Γ''
Pi = ΠP PiCon (ΠP PiA (ΠP PiB (El PiRet)))

Γ'''' : Con
Γ'''' = Γ''' ▶P Pi [ wk{P}{Γ''} ]TP
