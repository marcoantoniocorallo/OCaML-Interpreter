# OCaMLInterpreter
###### Progetto universitario per il corso di Programmazione II - Università di Pisa, a.a. 2018/2019

Il progetto ha l’obiettivo di applicare a casi specifici i concetti e le tecniche di implementazione dei linguaggi
di programmazione esaminate durante la seconda parte del corso. 
Il progetto consiste nella progettazione e realizzazione di un interprete per un semplice linguaggio di programmazione.
È richiesta l'estensione del linguaggio per poter manipolare come dati primitivi dizionari di elementi, ovvero una collezione di coppie (chiave, valore).
Nel progetto si definiscono:
- la sintassi concreta del linguaggio e la sintassi astratta tramite una opportuna definizione di tipo in OCaML
- l’interprete OCaMl del linguaggio funzionale assumendo la regola di scoping statico
- type checker dinamico del linguaggio risultante, in alternativa si può fornire il type checker statico del linguaggio
- una quantità di casi di test sufficiente a testare tutti gli operatori aggiuntivi.

È stata inoltre inserita la parte opzionale del progetto: un nuovo operatore rt_eval(exp) che interpreti il linguaggio funzionale assumendo la regola di scoping dinamico.
