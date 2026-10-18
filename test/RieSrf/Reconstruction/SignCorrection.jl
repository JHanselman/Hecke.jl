# The stored sign data and Fay relations: they load, and saving and loading
# again gives the same data.
@testset "Sign data and Fay relations" begin
  for g in 4:7
    pairs = RSM.load_sign_data(RSM._default_sign_data_file(g))
    @test !isempty(pairs)
    @test all(length(term) == 4 && nrows(M) == 2*g for (term, M) in pairs)
  end
  pairs = RSM.load_sign_data(RSM._default_sign_data_file(4))
  file = tempname()
  RSM.save_sign_data(file, pairs)
  again = RSM.load_sign_data(file)
  @test all(p[1] == q[1] && p[2] == q[2] for (p, q) in zip(pairs, again)) && length(pairs) == length(again)

  relations = RSM.load_fay_relations(RSM._default_fay_data_file(6))
  @test length(relations) == 2016 - 6 + 12
  RSM.save_fay_relations(file, relations)
  @test RSM.load_fay_relations(file) == relations
  rm(file)
end
