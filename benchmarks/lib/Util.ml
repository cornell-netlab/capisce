let pairs_app_dedup ~dedup (d1,c1) (d2,c2) =
  (dedup(d1 @ d2), dedup (c1 @ c2))
  
  
